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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
lean_object* lean_substring_drop(lean_object*, lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
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
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object*);
static lean_once_cell_t l_Lean_isIdFirstAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdFirstAscii___closed__0;
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object*);
static lean_once_cell_t l_Lean_isIdRestAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__0;
static lean_once_cell_t l_Lean_isIdRestAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__1;
static lean_once_cell_t l_Lean_isIdRestAscii___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__2;
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
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object*);
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
if (v___x_174_ == 0)
{
goto v___jp_162_;
}
else
{
return v___x_174_;
}
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
if (v___x_137_ == 0)
{
goto v___jp_128_;
}
else
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
if (v___x_166_ == 0)
{
goto v___jp_157_;
}
else
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
uint8_t v___y_218_; uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 65;
v___x_224_ = lean_uint32_dec_le(v___x_223_, v_c_212_);
if (v___x_224_ == 0)
{
v___y_218_ = v___x_224_;
goto v___jp_217_;
}
else
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 90;
v___x_226_ = lean_uint32_dec_le(v_c_212_, v___x_225_);
v___y_218_ = v___x_226_;
goto v___jp_217_;
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
if (v___y_218_ == 0)
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 97;
v___x_220_ = lean_uint32_dec_le(v___x_219_, v_c_212_);
if (v___x_220_ == 0)
{
goto v___jp_213_;
}
else
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 122;
v___x_222_ = lean_uint32_dec_le(v_c_212_, v___x_221_);
if (v___x_222_ == 0)
{
goto v___jp_213_;
}
else
{
return v___x_222_;
}
}
}
else
{
return v___y_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_227_){
_start:
{
uint32_t v_c_boxed_228_; uint8_t v_res_229_; lean_object* v_r_230_; 
v_c_boxed_228_ = lean_unbox_uint32(v_c_227_);
lean_dec(v_c_227_);
v_res_229_ = l_Lean_isIdFirst(v_c_boxed_228_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0(void){
_start:
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 65;
v___x_232_ = lean_uint32_to_uint8(v___x_231_);
return v___x_232_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1(void){
_start:
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 90;
v___x_234_ = lean_uint32_to_uint8(v___x_233_);
return v___x_234_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2(void){
_start:
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 97;
v___x_236_ = lean_uint32_to_uint8(v___x_235_);
return v___x_236_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3(void){
_start:
{
uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 122;
v___x_238_ = lean_uint32_to_uint8(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_239_){
_start:
{
uint8_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_246_ = lean_uint8_dec_le(v___x_245_, v_c_239_);
if (v___x_246_ == 0)
{
goto v___jp_240_;
}
else
{
uint8_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_248_ = lean_uint8_dec_le(v_c_239_, v___x_247_);
if (v___x_248_ == 0)
{
goto v___jp_240_;
}
else
{
return v___x_248_;
}
}
v___jp_240_:
{
uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_242_ = lean_uint8_dec_le(v___x_241_, v_c_239_);
if (v___x_242_ == 0)
{
return v___x_242_;
}
else
{
uint8_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_244_ = lean_uint8_dec_le(v_c_239_, v___x_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_249_){
_start:
{
uint8_t v_c_boxed_250_; uint8_t v_res_251_; lean_object* v_r_252_; 
v_c_boxed_250_ = lean_unbox(v_c_249_);
v_res_251_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0(void){
_start:
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 95;
v___x_254_ = lean_uint32_to_uint8(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_255_){
_start:
{
uint8_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_265_ = lean_uint8_dec_le(v___x_264_, v_c_255_);
if (v___x_265_ == 0)
{
goto v___jp_259_;
}
else
{
uint8_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_267_ = lean_uint8_dec_le(v_c_255_, v___x_266_);
if (v___x_267_ == 0)
{
goto v___jp_259_;
}
else
{
return v___x_267_;
}
}
v___jp_256_:
{
uint8_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_258_ = lean_uint8_dec_eq(v_c_255_, v___x_257_);
return v___x_258_;
}
v___jp_259_:
{
uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_261_ = lean_uint8_dec_le(v___x_260_, v_c_255_);
if (v___x_261_ == 0)
{
goto v___jp_256_;
}
else
{
uint8_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_263_ = lean_uint8_dec_le(v_c_255_, v___x_262_);
if (v___x_263_ == 0)
{
goto v___jp_256_;
}
else
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_268_){
_start:
{
uint8_t v_c_boxed_269_; uint8_t v_res_270_; lean_object* v_r_271_; 
v_c_boxed_269_ = lean_unbox(v_c_268_);
v_res_270_ = l_Lean_isIdFirstAscii(v_c_boxed_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0(void){
_start:
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 48;
v___x_273_ = lean_uint32_to_uint8(v___x_272_);
return v___x_273_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1(void){
_start:
{
uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 57;
v___x_275_ = lean_uint32_to_uint8(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_276_){
_start:
{
uint8_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_288_ = lean_uint8_dec_le(v___x_287_, v_c_276_);
if (v___x_288_ == 0)
{
goto v___jp_282_;
}
else
{
uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
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
v___x_278_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_279_ = lean_uint8_dec_le(v___x_278_, v_c_276_);
if (v___x_279_ == 0)
{
return v___x_279_;
}
else
{
uint8_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_281_ = lean_uint8_dec_le(v_c_276_, v___x_280_);
return v___x_281_;
}
}
v___jp_282_:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_276_);
if (v___x_284_ == 0)
{
goto v___jp_277_;
}
else
{
uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_291_){
_start:
{
uint8_t v_c_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_c_boxed_292_ = lean_unbox(v_c_291_);
v_res_293_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_295_){
_start:
{
uint8_t v___y_313_; uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 65;
v___x_319_ = lean_uint32_dec_le(v___x_318_, v_c_295_);
if (v___x_319_ == 0)
{
v___y_313_ = v___x_319_;
goto v___jp_312_;
}
else
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 90;
v___x_321_ = lean_uint32_dec_le(v_c_295_, v___x_320_);
v___y_313_ = v___x_321_;
goto v___jp_312_;
}
v___jp_296_:
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 95;
v___x_298_ = lean_uint32_dec_eq(v_c_295_, v___x_297_);
if (v___x_298_ == 0)
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 39;
v___x_300_ = lean_uint32_dec_eq(v_c_295_, v___x_299_);
if (v___x_300_ == 0)
{
uint32_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 33;
v___x_302_ = lean_uint32_dec_eq(v_c_295_, v___x_301_);
if (v___x_302_ == 0)
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 63;
v___x_304_ = lean_uint32_dec_eq(v_c_295_, v___x_303_);
if (v___x_304_ == 0)
{
uint8_t v___x_305_; 
v___x_305_ = l_Lean_isLetterLike(v_c_295_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_isSubScriptAlnum(v_c_295_);
return v___x_306_;
}
else
{
return v___x_305_;
}
}
else
{
return v___x_304_;
}
}
else
{
return v___x_302_;
}
}
else
{
return v___x_300_;
}
}
else
{
return v___x_298_;
}
}
v___jp_307_:
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 48;
v___x_309_ = lean_uint32_dec_le(v___x_308_, v_c_295_);
if (v___x_309_ == 0)
{
goto v___jp_296_;
}
else
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 57;
v___x_311_ = lean_uint32_dec_le(v_c_295_, v___x_310_);
if (v___x_311_ == 0)
{
goto v___jp_296_;
}
else
{
return v___x_311_;
}
}
}
v___jp_312_:
{
if (v___y_313_ == 0)
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 97;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v_c_295_);
if (v___x_315_ == 0)
{
goto v___jp_307_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 122;
v___x_317_ = lean_uint32_dec_le(v_c_295_, v___x_316_);
if (v___x_317_ == 0)
{
goto v___jp_307_;
}
else
{
return v___x_317_;
}
}
}
else
{
return v___y_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_322_){
_start:
{
uint32_t v_c_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_c_boxed_323_ = lean_unbox_uint32(v_c_322_);
lean_dec(v_c_322_);
v_res_324_ = l_Lean_isIdRest(v_c_boxed_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0(void){
_start:
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 39;
v___x_327_ = lean_uint32_to_uint8(v___x_326_);
return v___x_327_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1(void){
_start:
{
uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 33;
v___x_329_ = lean_uint32_to_uint8(v___x_328_);
return v___x_329_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2(void){
_start:
{
uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 63;
v___x_331_ = lean_uint32_to_uint8(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_332_){
_start:
{
uint8_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_353_ = lean_uint8_dec_le(v___x_352_, v_c_332_);
if (v___x_353_ == 0)
{
goto v___jp_347_;
}
else
{
uint8_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_355_ = lean_uint8_dec_le(v_c_332_, v___x_354_);
if (v___x_355_ == 0)
{
goto v___jp_347_;
}
else
{
return v___x_355_;
}
}
v___jp_333_:
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_335_ = lean_uint8_dec_eq(v_c_332_, v___x_334_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_337_ = lean_uint8_dec_eq(v_c_332_, v___x_336_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_339_ = lean_uint8_dec_eq(v_c_332_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_341_ = lean_uint8_dec_eq(v_c_332_, v___x_340_);
return v___x_341_;
}
else
{
return v___x_339_;
}
}
else
{
return v___x_337_;
}
}
else
{
return v___x_335_;
}
}
v___jp_342_:
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_344_ = lean_uint8_dec_le(v___x_343_, v_c_332_);
if (v___x_344_ == 0)
{
goto v___jp_333_;
}
else
{
uint8_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_346_ = lean_uint8_dec_le(v_c_332_, v___x_345_);
if (v___x_346_ == 0)
{
goto v___jp_333_;
}
else
{
return v___x_346_;
}
}
}
v___jp_347_:
{
uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_349_ = lean_uint8_dec_le(v___x_348_, v_c_332_);
if (v___x_349_ == 0)
{
goto v___jp_342_;
}
else
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_351_ = lean_uint8_dec_le(v_c_332_, v___x_350_);
if (v___x_351_ == 0)
{
goto v___jp_342_;
}
else
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_356_){
_start:
{
uint8_t v_c_boxed_357_; uint8_t v_res_358_; lean_object* v_r_359_; 
v_c_boxed_357_ = lean_unbox(v_c_356_);
v_res_358_ = l_Lean_isIdRestAscii(v_c_boxed_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_360_; 
v___x_360_ = 171;
return v___x_360_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_361_; 
v___x_361_ = 187;
return v___x_361_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_362_){
_start:
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 171;
v___x_364_ = lean_uint32_dec_eq(v_c_362_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_365_){
_start:
{
uint32_t v_c_boxed_366_; uint8_t v_res_367_; lean_object* v_r_368_; 
v_c_boxed_366_ = lean_unbox_uint32(v_c_365_);
lean_dec(v_c_365_);
v_res_367_ = l_Lean_isIdBeginEscape(v_c_boxed_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_369_){
_start:
{
uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 187;
v___x_371_ = lean_uint32_dec_eq(v_c_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_372_){
_start:
{
uint32_t v_c_boxed_373_; uint8_t v_res_374_; lean_object* v_r_375_; 
v_c_boxed_373_ = lean_unbox_uint32(v_c_372_);
lean_dec(v_c_372_);
v_res_374_ = l_Lean_isIdEndEscape(v_c_boxed_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
return v_x_376_;
}
else
{
lean_object* v_pre_377_; 
v_pre_377_ = lean_ctor_get(v_x_376_, 0);
if (lean_obj_tag(v_pre_377_) == 0)
{
lean_inc(v_x_376_);
return v_x_376_;
}
else
{
v_x_376_ = v_pre_377_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Name_getRoot(v_x_379_);
lean_dec(v_x_379_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_382_){
_start:
{
switch(lean_obj_tag(v_x_382_))
{
case 1:
{
lean_object* v_str_383_; uint32_t v___x_384_; uint8_t v___x_385_; 
v_str_383_ = lean_ctor_get(v_x_382_, 1);
lean_inc_ref_n(v_str_383_, 2);
lean_dec_ref_known(v_x_382_, 2);
v___x_384_ = 10013;
v___x_385_ = lean_string_contains(v_str_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_387_ = lean_string_dec_eq(v_str_383_, v___x_386_);
lean_dec_ref(v_str_383_);
return v___x_387_;
}
else
{
lean_dec_ref(v_str_383_);
return v___x_385_;
}
}
case 2:
{
lean_object* v_pre_388_; 
v_pre_388_ = lean_ctor_get(v_x_382_, 0);
lean_inc(v_pre_388_);
lean_dec_ref_known(v_x_382_, 2);
v_x_382_ = v_pre_388_;
goto _start;
}
default: 
{
uint8_t v___x_390_; 
lean_dec(v_x_382_);
v___x_390_ = 0;
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_Name_isInaccessibleUserName(v_x_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_394_, lean_object* v_i_395_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_string_utf8_byte_size(v_s_394_);
v___x_401_ = lean_nat_dec_lt(v_i_395_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; 
lean_dec(v_i_395_);
v___x_402_ = 1;
return v___x_402_;
}
else
{
uint8_t v_c_403_; uint8_t v___x_423_; uint8_t v___x_424_; 
lean_inc(v_i_395_);
v_c_403_ = lean_string_get_byte_fast(v_s_394_, v_i_395_);
v___x_423_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_424_ = lean_uint8_dec_le(v___x_423_, v_c_403_);
if (v___x_424_ == 0)
{
goto v___jp_418_;
}
else
{
uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_426_ = lean_uint8_dec_le(v_c_403_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_418_;
}
else
{
goto v___jp_396_;
}
}
v___jp_404_:
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_406_ = lean_uint8_dec_eq(v_c_403_, v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_408_ = lean_uint8_dec_eq(v_c_403_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_410_ = lean_uint8_dec_eq(v_c_403_, v___x_409_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_412_ = lean_uint8_dec_eq(v_c_403_, v___x_411_);
if (v___x_412_ == 0)
{
lean_dec(v_i_395_);
return v___x_412_;
}
else
{
goto v___jp_396_;
}
}
else
{
goto v___jp_396_;
}
}
else
{
goto v___jp_396_;
}
}
else
{
goto v___jp_396_;
}
}
v___jp_413_:
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_415_ = lean_uint8_dec_le(v___x_414_, v_c_403_);
if (v___x_415_ == 0)
{
goto v___jp_404_;
}
else
{
uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_417_ = lean_uint8_dec_le(v_c_403_, v___x_416_);
if (v___x_417_ == 0)
{
goto v___jp_404_;
}
else
{
goto v___jp_396_;
}
}
}
v___jp_418_:
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_c_403_);
if (v___x_420_ == 0)
{
goto v___jp_413_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_422_ = lean_uint8_dec_le(v_c_403_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_413_;
}
else
{
goto v___jp_396_;
}
}
}
}
v___jp_396_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_i_395_, v___x_397_);
lean_dec(v_i_395_);
v_i_395_ = v___x_398_;
goto _start;
}
}
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
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_431_){
_start:
{
lean_object* v___x_435_; uint8_t v_c_436_; uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v_c_436_ = lean_string_get_byte_fast(v_s_431_, v___x_435_);
v___x_445_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_446_ = lean_uint8_dec_le(v___x_445_, v_c_436_);
if (v___x_446_ == 0)
{
goto v___jp_440_;
}
else
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
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
v___x_438_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
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
v___x_441_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_442_ = lean_uint8_dec_le(v___x_441_, v_c_436_);
if (v___x_442_ == 0)
{
goto v___jp_437_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_449_);
lean_dec_ref(v_s_449_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_452_, lean_object* v_h_453_){
_start:
{
lean_object* v___x_457_; uint8_t v_c_458_; uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v_c_458_ = lean_string_get_byte_fast(v_s_452_, v___x_457_);
v___x_467_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_468_ = lean_uint8_dec_le(v___x_467_, v_c_458_);
if (v___x_468_ == 0)
{
goto v___jp_462_;
}
else
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_470_ = lean_uint8_dec_le(v_c_458_, v___x_469_);
if (v___x_470_ == 0)
{
goto v___jp_462_;
}
else
{
goto v___jp_454_;
}
}
v___jp_454_:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_452_, v___x_455_);
return v___x_456_;
}
v___jp_459_:
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_461_ = lean_uint8_dec_eq(v_c_458_, v___x_460_);
if (v___x_461_ == 0)
{
return v___x_461_;
}
else
{
goto v___jp_454_;
}
}
v___jp_462_:
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_464_ = lean_uint8_dec_le(v___x_463_, v_c_458_);
if (v___x_464_ == 0)
{
goto v___jp_459_;
}
else
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_466_ = lean_uint8_dec_le(v_c_458_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_459_;
}
else
{
goto v___jp_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_471_, lean_object* v_h_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_471_, v_h_472_);
lean_dec_ref(v_s_471_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_476_){
_start:
{
uint32_t v___y_486_; uint32_t v___y_491_; uint8_t v___y_492_; lean_object* v___x_507_; uint8_t v_c_508_; uint8_t v___x_517_; uint8_t v___x_518_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v_c_508_ = lean_string_get_byte_fast(v_s_476_, v___x_507_);
v___x_517_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_518_ = lean_uint8_dec_le(v___x_517_, v_c_508_);
if (v___x_518_ == 0)
{
goto v___jp_512_;
}
else
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_520_ = lean_uint8_dec_le(v_c_508_, v___x_519_);
if (v___x_520_ == 0)
{
goto v___jp_512_;
}
else
{
goto v___jp_504_;
}
}
v___jp_477_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_string_utf8_byte_size(v_s_476_);
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v_s_476_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_substring_drop(v___x_480_, v___x_481_);
v___x_483_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_484_ = lean_substring_all(v___x_482_, v___x_483_);
return v___x_484_;
}
v___jp_485_:
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 95;
v___x_488_ = lean_uint32_dec_eq(v___y_486_, v___x_487_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; 
v___x_489_ = l_Lean_isLetterLike(v___y_486_);
if (v___x_489_ == 0)
{
lean_dec_ref(v_s_476_);
return v___x_489_;
}
else
{
goto v___jp_477_;
}
}
else
{
goto v___jp_477_;
}
}
v___jp_490_:
{
if (v___y_492_ == 0)
{
uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 97;
v___x_494_ = lean_uint32_dec_le(v___x_493_, v___y_491_);
if (v___x_494_ == 0)
{
v___y_486_ = v___y_491_;
goto v___jp_485_;
}
else
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 122;
v___x_496_ = lean_uint32_dec_le(v___y_491_, v___x_495_);
if (v___x_496_ == 0)
{
v___y_486_ = v___y_491_;
goto v___jp_485_;
}
else
{
goto v___jp_477_;
}
}
}
else
{
goto v___jp_477_;
}
}
v___jp_497_:
{
lean_object* v___x_498_; uint32_t v___x_499_; uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_string_utf8_get(v_s_476_, v___x_498_);
v___x_500_ = 65;
v___x_501_ = lean_uint32_dec_le(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
v___y_491_ = v___x_499_;
v___y_492_ = v___x_501_;
goto v___jp_490_;
}
else
{
uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 90;
v___x_503_ = lean_uint32_dec_le(v___x_499_, v___x_502_);
v___y_491_ = v___x_499_;
v___y_492_ = v___x_503_;
goto v___jp_490_;
}
}
v___jp_504_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_476_, v___x_505_);
if (v___x_506_ == 0)
{
goto v___jp_497_;
}
else
{
lean_dec_ref(v_s_476_);
return v___x_506_;
}
}
v___jp_509_:
{
uint8_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_511_ = lean_uint8_dec_eq(v_c_508_, v___x_510_);
if (v___x_511_ == 0)
{
goto v___jp_497_;
}
else
{
goto v___jp_504_;
}
}
v___jp_512_:
{
uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_514_ = lean_uint8_dec_le(v___x_513_, v_c_508_);
if (v___x_514_ == 0)
{
goto v___jp_509_;
}
else
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_516_ = lean_uint8_dec_le(v_c_508_, v___x_515_);
if (v___x_516_ == 0)
{
goto v___jp_509_;
}
else
{
goto v___jp_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_521_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_524_, lean_object* v_h_525_){
_start:
{
uint32_t v___y_535_; uint32_t v___y_540_; uint8_t v___y_541_; lean_object* v___x_556_; uint8_t v_c_557_; uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v_c_557_ = lean_string_get_byte_fast(v_s_524_, v___x_556_);
v___x_566_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_567_ = lean_uint8_dec_le(v___x_566_, v_c_557_);
if (v___x_567_ == 0)
{
goto v___jp_561_;
}
else
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_569_ = lean_uint8_dec_le(v_c_557_, v___x_568_);
if (v___x_569_ == 0)
{
goto v___jp_561_;
}
else
{
goto v___jp_553_;
}
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_string_utf8_byte_size(v_s_524_);
v___x_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_529_, 0, v_s_524_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_substring_drop(v___x_529_, v___x_530_);
v___x_532_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_533_ = lean_substring_all(v___x_531_, v___x_532_);
return v___x_533_;
}
v___jp_534_:
{
uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 95;
v___x_537_ = lean_uint32_dec_eq(v___y_535_, v___x_536_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_isLetterLike(v___y_535_);
if (v___x_538_ == 0)
{
lean_dec_ref(v_s_524_);
return v___x_538_;
}
else
{
goto v___jp_526_;
}
}
else
{
goto v___jp_526_;
}
}
v___jp_539_:
{
if (v___y_541_ == 0)
{
uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 97;
v___x_543_ = lean_uint32_dec_le(v___x_542_, v___y_540_);
if (v___x_543_ == 0)
{
v___y_535_ = v___y_540_;
goto v___jp_534_;
}
else
{
uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 122;
v___x_545_ = lean_uint32_dec_le(v___y_540_, v___x_544_);
if (v___x_545_ == 0)
{
v___y_535_ = v___y_540_;
goto v___jp_534_;
}
else
{
goto v___jp_526_;
}
}
}
else
{
goto v___jp_526_;
}
}
v___jp_546_:
{
lean_object* v___x_547_; uint32_t v___x_548_; uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_string_utf8_get(v_s_524_, v___x_547_);
v___x_549_ = 65;
v___x_550_ = lean_uint32_dec_le(v___x_549_, v___x_548_);
if (v___x_550_ == 0)
{
v___y_540_ = v___x_548_;
v___y_541_ = v___x_550_;
goto v___jp_539_;
}
else
{
uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 90;
v___x_552_ = lean_uint32_dec_le(v___x_548_, v___x_551_);
v___y_540_ = v___x_548_;
v___y_541_ = v___x_552_;
goto v___jp_539_;
}
}
v___jp_553_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_524_, v___x_554_);
if (v___x_555_ == 0)
{
goto v___jp_546_;
}
else
{
lean_dec_ref(v_s_524_);
return v___x_555_;
}
}
v___jp_558_:
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_560_ = lean_uint8_dec_eq(v_c_557_, v___x_559_);
if (v___x_560_ == 0)
{
goto v___jp_546_;
}
else
{
goto v___jp_553_;
}
}
v___jp_561_:
{
uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_563_ = lean_uint8_dec_le(v___x_562_, v_c_557_);
if (v___x_563_ == 0)
{
goto v___jp_558_;
}
else
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_565_ = lean_uint8_dec_le(v_c_557_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_558_;
}
else
{
goto v___jp_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_570_, lean_object* v_h_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_570_, v_h_571_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0(void){
_start:
{
uint32_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = 171;
v___x_575_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_576_ = lean_string_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = 187;
v___x_578_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_579_ = lean_string_push(v___x_578_, v___x_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_582_ = lean_string_append(v___x_581_, v_s_580_);
v___x_583_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_585_);
lean_dec_ref(v_s_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_588_, uint8_t v_force_589_){
_start:
{
uint8_t v___y_600_; uint32_t v___y_611_; uint32_t v___y_616_; uint8_t v___y_617_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_string_utf8_byte_size(v_s_588_);
v___x_634_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_636_ = lean_string_append(v___x_635_, v_s_588_);
lean_dec_ref(v_s_588_);
v___x_637_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_638_ = lean_string_append(v___x_636_, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
else
{
if (v_force_589_ == 0)
{
uint8_t v_c_640_; uint8_t v___x_649_; uint8_t v___x_650_; 
v_c_640_ = lean_string_get_byte_fast(v_s_588_, v___x_632_);
v___x_649_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_650_ = lean_uint8_dec_le(v___x_649_, v_c_640_);
if (v___x_650_ == 0)
{
goto v___jp_644_;
}
else
{
uint8_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_652_ = lean_uint8_dec_le(v_c_640_, v___x_651_);
if (v___x_652_ == 0)
{
goto v___jp_644_;
}
else
{
goto v___jp_629_;
}
}
v___jp_641_:
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_643_ = lean_uint8_dec_eq(v_c_640_, v___x_642_);
if (v___x_643_ == 0)
{
goto v___jp_622_;
}
else
{
goto v___jp_629_;
}
}
v___jp_644_:
{
uint8_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_646_ = lean_uint8_dec_le(v___x_645_, v_c_640_);
if (v___x_646_ == 0)
{
goto v___jp_641_;
}
else
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_648_ = lean_uint8_dec_le(v_c_640_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_641_;
}
else
{
goto v___jp_629_;
}
}
}
}
else
{
goto v___jp_590_;
}
}
v___jp_590_:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_588_);
v___x_592_ = lean_string_any(v_s_588_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_593_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_594_ = lean_string_append(v___x_593_, v_s_588_);
lean_dec_ref(v_s_588_);
v___x_595_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; 
lean_dec_ref(v_s_588_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
}
v___jp_599_:
{
if (v___y_600_ == 0)
{
goto v___jp_590_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_s_588_);
return v___x_601_;
}
}
v___jp_602_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_string_utf8_byte_size(v_s_588_);
lean_inc_ref(v_s_588_);
v___x_605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_605_, 0, v_s_588_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
lean_ctor_set(v___x_605_, 2, v___x_604_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_substring_drop(v___x_605_, v___x_606_);
v___x_608_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_609_ = lean_substring_all(v___x_607_, v___x_608_);
v___y_600_ = v___x_609_;
goto v___jp_599_;
}
v___jp_610_:
{
uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 95;
v___x_613_ = lean_uint32_dec_eq(v___y_611_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_isLetterLike(v___y_611_);
if (v___x_614_ == 0)
{
v___y_600_ = v___x_614_;
goto v___jp_599_;
}
else
{
goto v___jp_602_;
}
}
else
{
goto v___jp_602_;
}
}
v___jp_615_:
{
if (v___y_617_ == 0)
{
uint32_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 97;
v___x_619_ = lean_uint32_dec_le(v___x_618_, v___y_616_);
if (v___x_619_ == 0)
{
v___y_611_ = v___y_616_;
goto v___jp_610_;
}
else
{
uint32_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 122;
v___x_621_ = lean_uint32_dec_le(v___y_616_, v___x_620_);
if (v___x_621_ == 0)
{
v___y_611_ = v___y_616_;
goto v___jp_610_;
}
else
{
goto v___jp_602_;
}
}
}
else
{
goto v___jp_602_;
}
}
v___jp_622_:
{
lean_object* v___x_623_; uint32_t v___x_624_; uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_string_utf8_get(v_s_588_, v___x_623_);
v___x_625_ = 65;
v___x_626_ = lean_uint32_dec_le(v___x_625_, v___x_624_);
if (v___x_626_ == 0)
{
v___y_616_ = v___x_624_;
v___y_617_ = v___x_626_;
goto v___jp_615_;
}
else
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 90;
v___x_628_ = lean_uint32_dec_le(v___x_624_, v___x_627_);
v___y_616_ = v___x_624_;
v___y_617_ = v___x_628_;
goto v___jp_615_;
}
}
v___jp_629_:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_588_, v___x_630_);
if (v___x_631_ == 0)
{
goto v___jp_622_;
}
else
{
v___y_600_ = v___x_631_;
goto v___jp_599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_653_, lean_object* v_force_654_){
_start:
{
uint8_t v_force_boxed_655_; lean_object* v_res_656_; 
v_force_boxed_655_ = lean_unbox(v_force_654_);
v_res_656_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_653_, v_force_boxed_655_);
return v_res_656_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_657_){
_start:
{
uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 187;
v___x_659_ = lean_uint32_dec_eq(v___y_657_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_660_){
_start:
{
uint32_t v___y_284__boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v___y_284__boxed_661_ = lean_unbox_uint32(v___y_660_);
lean_dec(v___y_660_);
v_res_662_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_284__boxed_661_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_664_){
_start:
{
uint8_t v___y_682_; uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 65;
v___x_688_ = lean_uint32_dec_le(v___x_687_, v___y_664_);
if (v___x_688_ == 0)
{
v___y_682_ = v___x_688_;
goto v___jp_681_;
}
else
{
uint32_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = 90;
v___x_690_ = lean_uint32_dec_le(v___y_664_, v___x_689_);
v___y_682_ = v___x_690_;
goto v___jp_681_;
}
v___jp_665_:
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 95;
v___x_667_ = lean_uint32_dec_eq(v___y_664_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 39;
v___x_669_ = lean_uint32_dec_eq(v___y_664_, v___x_668_);
if (v___x_669_ == 0)
{
uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 33;
v___x_671_ = lean_uint32_dec_eq(v___y_664_, v___x_670_);
if (v___x_671_ == 0)
{
uint32_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = 63;
v___x_673_ = lean_uint32_dec_eq(v___y_664_, v___x_672_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_isLetterLike(v___y_664_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
v___x_675_ = l_Lean_isSubScriptAlnum(v___y_664_);
return v___x_675_;
}
else
{
return v___x_674_;
}
}
else
{
return v___x_673_;
}
}
else
{
return v___x_671_;
}
}
else
{
return v___x_669_;
}
}
else
{
return v___x_667_;
}
}
v___jp_676_:
{
uint32_t v___x_677_; uint8_t v___x_678_; 
v___x_677_ = 48;
v___x_678_ = lean_uint32_dec_le(v___x_677_, v___y_664_);
if (v___x_678_ == 0)
{
goto v___jp_665_;
}
else
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 57;
v___x_680_ = lean_uint32_dec_le(v___y_664_, v___x_679_);
if (v___x_680_ == 0)
{
goto v___jp_665_;
}
else
{
return v___x_680_;
}
}
}
v___jp_681_:
{
if (v___y_682_ == 0)
{
uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 97;
v___x_684_ = lean_uint32_dec_le(v___x_683_, v___y_664_);
if (v___x_684_ == 0)
{
goto v___jp_676_;
}
else
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 122;
v___x_686_ = lean_uint32_dec_le(v___y_664_, v___x_685_);
if (v___x_686_ == 0)
{
goto v___jp_676_;
}
else
{
return v___x_686_;
}
}
}
else
{
return v___y_682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_691_){
_start:
{
uint32_t v___y_291__boxed_692_; uint8_t v_res_693_; lean_object* v_r_694_; 
v___y_291__boxed_692_ = lean_unbox_uint32(v___y_691_);
lean_dec(v___y_691_);
v_res_693_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_291__boxed_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_697_, lean_object* v_s_698_, uint8_t v_force_699_){
_start:
{
if (v_escape_697_ == 0)
{
return v_s_698_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_string_utf8_byte_size(v_s_698_);
v___x_702_ = lean_nat_dec_lt(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_704_ = lean_string_append(v___x_703_, v_s_698_);
lean_dec_ref(v_s_698_);
v___x_705_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___f_707_; uint8_t v___y_715_; 
v___f_707_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_699_ == 0)
{
lean_object* v___f_716_; uint32_t v___y_723_; uint32_t v___y_728_; uint8_t v___y_729_; uint8_t v_c_743_; uint8_t v___x_752_; uint8_t v___x_753_; 
v___f_716_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_743_ = lean_string_get_byte_fast(v_s_698_, v___x_700_);
v___x_752_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_753_ = lean_uint8_dec_le(v___x_752_, v_c_743_);
if (v___x_753_ == 0)
{
goto v___jp_747_;
}
else
{
uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_755_ = lean_uint8_dec_le(v_c_743_, v___x_754_);
if (v___x_755_ == 0)
{
goto v___jp_747_;
}
else
{
goto v___jp_740_;
}
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
lean_inc_ref(v_s_698_);
v___x_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_718_, 0, v_s_698_);
lean_ctor_set(v___x_718_, 1, v___x_700_);
lean_ctor_set(v___x_718_, 2, v___x_701_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_substring_drop(v___x_718_, v___x_719_);
v___x_721_ = lean_substring_all(v___x_720_, v___f_716_);
v___y_715_ = v___x_721_;
goto v___jp_714_;
}
v___jp_722_:
{
uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 95;
v___x_725_ = lean_uint32_dec_eq(v___y_723_, v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_isLetterLike(v___y_723_);
if (v___x_726_ == 0)
{
v___y_715_ = v___x_726_;
goto v___jp_714_;
}
else
{
goto v___jp_717_;
}
}
else
{
goto v___jp_717_;
}
}
v___jp_727_:
{
if (v___y_729_ == 0)
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 97;
v___x_731_ = lean_uint32_dec_le(v___x_730_, v___y_728_);
if (v___x_731_ == 0)
{
v___y_723_ = v___y_728_;
goto v___jp_722_;
}
else
{
uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 122;
v___x_733_ = lean_uint32_dec_le(v___y_728_, v___x_732_);
if (v___x_733_ == 0)
{
v___y_723_ = v___y_728_;
goto v___jp_722_;
}
else
{
goto v___jp_717_;
}
}
}
else
{
goto v___jp_717_;
}
}
v___jp_734_:
{
uint32_t v___x_735_; uint32_t v___x_736_; uint8_t v___x_737_; 
v___x_735_ = lean_string_utf8_get(v_s_698_, v___x_700_);
v___x_736_ = 65;
v___x_737_ = lean_uint32_dec_le(v___x_736_, v___x_735_);
if (v___x_737_ == 0)
{
v___y_728_ = v___x_735_;
v___y_729_ = v___x_737_;
goto v___jp_727_;
}
else
{
uint32_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = 90;
v___x_739_ = lean_uint32_dec_le(v___x_735_, v___x_738_);
v___y_728_ = v___x_735_;
v___y_729_ = v___x_739_;
goto v___jp_727_;
}
}
v___jp_740_:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_698_, v___x_741_);
if (v___x_742_ == 0)
{
goto v___jp_734_;
}
else
{
v___y_715_ = v___x_742_;
goto v___jp_714_;
}
}
v___jp_744_:
{
uint8_t v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_746_ = lean_uint8_dec_eq(v_c_743_, v___x_745_);
if (v___x_746_ == 0)
{
goto v___jp_734_;
}
else
{
goto v___jp_740_;
}
}
v___jp_747_:
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_749_ = lean_uint8_dec_le(v___x_748_, v_c_743_);
if (v___x_749_ == 0)
{
goto v___jp_744_;
}
else
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_751_ = lean_uint8_dec_le(v_c_743_, v___x_750_);
if (v___x_751_ == 0)
{
goto v___jp_744_;
}
else
{
goto v___jp_740_;
}
}
}
}
else
{
goto v___jp_708_;
}
v___jp_708_:
{
uint8_t v___x_709_; 
lean_inc_ref(v_s_698_);
v___x_709_ = lean_string_any(v_s_698_, v___f_707_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_711_ = lean_string_append(v___x_710_, v_s_698_);
lean_dec_ref(v_s_698_);
v___x_712_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
return v___x_713_;
}
else
{
return v_s_698_;
}
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
goto v___jp_708_;
}
else
{
return v_s_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_756_, lean_object* v_s_757_, lean_object* v_force_758_){
_start:
{
uint8_t v_escape_boxed_759_; uint8_t v_force_boxed_760_; lean_object* v_res_761_; 
v_escape_boxed_759_ = lean_unbox(v_escape_756_);
v_force_boxed_760_ = lean_unbox(v_force_758_);
v_res_761_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_759_, v_s_757_, v_force_boxed_760_);
return v_res_761_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_769_, uint8_t v_escape_770_, lean_object* v_n_771_, lean_object* v_isToken_772_){
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_798_, lean_object* v_escape_799_, lean_object* v_n_800_, lean_object* v_isToken_801_){
_start:
{
uint8_t v_escape_boxed_802_; lean_object* v_res_803_; 
v_escape_boxed_802_ = lean_unbox(v_escape_799_);
v_res_803_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_798_, v_escape_boxed_802_, v_n_800_, v_isToken_801_);
lean_dec_ref(v_sep_798_);
return v_res_803_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_809_){
_start:
{
lean_object* v___x_810_; uint8_t v___x_811_; uint8_t v___x_812_; 
v___x_810_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_811_ = lean_name_eq(v_n_809_, v___x_810_);
v___x_812_ = 1;
if (v___x_811_ == 0)
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Name_getRoot(v_n_809_);
if (lean_obj_tag(v___x_813_) == 1)
{
lean_object* v_str_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_str_814_ = lean_ctor_get(v___x_813_, 1);
lean_inc_ref_n(v_str_814_, 2);
lean_dec_ref_known(v___x_813_, 2);
v___x_815_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_816_ = lean_string_isprefixof(v___x_815_, v_str_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_818_ = lean_string_isprefixof(v___x_817_, v_str_814_);
return v___x_818_;
}
else
{
lean_dec_ref(v_str_814_);
return v___x_812_;
}
}
else
{
lean_dec(v___x_813_);
return v___x_811_;
}
}
else
{
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_819_);
lean_dec(v_n_819_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_822_, uint8_t v_escape_823_, lean_object* v_isToken_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_823_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_825_, v_escape_823_, v_n_822_, v_isToken_824_);
return v___x_826_;
}
else
{
uint8_t v___x_827_; 
lean_inc(v_n_822_);
v___x_827_ = l_Lean_Name_isInaccessibleUserName(v_n_822_);
if (v___x_827_ == 0)
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_Name_hasMacroScopes(v_n_822_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_822_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_825_, v_escape_823_, v_n_822_, v_isToken_824_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_825_, v___x_828_, v_n_822_, v_isToken_824_);
return v___x_831_;
}
}
else
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_825_, v___x_827_, v_n_822_, v_isToken_824_);
return v___x_832_;
}
}
else
{
uint8_t v___x_833_; lean_object* v___x_834_; 
v___x_833_ = 0;
v___x_834_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_825_, v___x_833_, v_n_822_, v_isToken_824_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_835_, lean_object* v_escape_836_, lean_object* v_isToken_837_){
_start:
{
uint8_t v_escape_boxed_838_; lean_object* v_res_839_; 
v_escape_boxed_838_ = lean_unbox(v_escape_836_);
v_res_839_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_835_, v_escape_boxed_838_, v_isToken_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_840_, uint8_t v_escape_841_, lean_object* v_n_842_){
_start:
{
switch(lean_obj_tag(v_n_842_))
{
case 0:
{
lean_object* v___x_843_; 
v___x_843_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_843_;
}
case 1:
{
lean_object* v_pre_844_; 
v_pre_844_ = lean_ctor_get(v_n_842_, 0);
if (lean_obj_tag(v_pre_844_) == 0)
{
lean_object* v_str_845_; uint8_t v___x_846_; lean_object* v___x_847_; 
v_str_845_ = lean_ctor_get(v_n_842_, 1);
lean_inc_ref(v_str_845_);
lean_dec_ref_known(v_n_842_, 2);
v___x_846_ = 0;
v___x_847_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_841_, v_str_845_, v___x_846_);
return v___x_847_;
}
else
{
lean_object* v_str_848_; lean_object* v_r_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v_r_x27_853_; 
lean_inc(v_pre_844_);
v_str_848_ = lean_ctor_get(v_n_842_, 1);
lean_inc_ref(v_str_848_);
lean_dec_ref_known(v_n_842_, 2);
v_r_849_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_840_, v_escape_841_, v_pre_844_);
v___x_850_ = lean_string_append(v_r_849_, v_sep_840_);
v___x_851_ = 0;
v___x_852_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_841_, v_str_848_, v___x_851_);
v_r_x27_853_ = lean_string_append(v___x_850_, v___x_852_);
lean_dec_ref(v___x_852_);
return v_r_x27_853_;
}
}
default: 
{
lean_object* v_pre_854_; 
v_pre_854_ = lean_ctor_get(v_n_842_, 0);
if (lean_obj_tag(v_pre_854_) == 0)
{
lean_object* v_i_855_; lean_object* v___x_856_; 
v_i_855_ = lean_ctor_get(v_n_842_, 1);
lean_inc(v_i_855_);
lean_dec_ref_known(v_n_842_, 2);
v___x_856_ = l_Nat_reprFast(v_i_855_);
return v___x_856_;
}
else
{
lean_object* v_i_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc(v_pre_854_);
v_i_857_ = lean_ctor_get(v_n_842_, 1);
lean_inc(v_i_857_);
lean_dec_ref_known(v_n_842_, 2);
v___x_858_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_840_, v_escape_841_, v_pre_854_);
v___x_859_ = lean_string_append(v___x_858_, v_sep_840_);
v___x_860_ = l_Nat_reprFast(v_i_857_);
v___x_861_ = lean_string_append(v___x_859_, v___x_860_);
lean_dec_ref(v___x_860_);
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_862_, lean_object* v_escape_863_, lean_object* v_n_864_){
_start:
{
uint8_t v_escape_boxed_865_; lean_object* v_res_866_; 
v_escape_boxed_865_ = lean_unbox(v_escape_863_);
v_res_866_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_862_, v_escape_boxed_865_, v_n_864_);
lean_dec_ref(v_sep_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_867_, uint8_t v_escape_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_868_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_869_, v_escape_868_, v_n_867_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; 
lean_inc(v_n_867_);
v___x_871_ = l_Lean_Name_isInaccessibleUserName(v_n_867_);
if (v___x_871_ == 0)
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_Name_hasMacroScopes(v_n_867_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_867_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_869_, v_escape_868_, v_n_867_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_869_, v___x_872_, v_n_867_);
return v___x_875_;
}
}
else
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_869_, v___x_871_, v_n_867_);
return v___x_876_;
}
}
else
{
uint8_t v___x_877_; lean_object* v___x_878_; 
v___x_877_ = 0;
v___x_878_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_869_, v___x_877_, v_n_867_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_879_, lean_object* v_escape_880_){
_start:
{
uint8_t v_escape_boxed_881_; lean_object* v_res_882_; 
v_escape_boxed_881_ = lean_unbox(v_escape_880_);
v_res_882_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_879_, v_escape_boxed_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_883_, uint8_t v_escape_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_883_, v_escape_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_886_, lean_object* v_escape_887_){
_start:
{
uint8_t v_escape_boxed_888_; lean_object* v_res_889_; 
v_escape_boxed_888_ = lean_unbox(v_escape_887_);
v_res_889_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_886_, v_escape_boxed_888_);
return v_res_889_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_890_){
_start:
{
switch(lean_obj_tag(v_x_890_))
{
case 0:
{
uint8_t v___x_891_; 
v___x_891_ = 0;
return v___x_891_;
}
case 1:
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_x_890_, 0);
v_x_890_ = v_pre_892_;
goto _start;
}
default: 
{
uint8_t v___x_894_; 
v___x_894_ = 1;
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_895_);
lean_dec(v_x_895_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_913_, lean_object* v_prec_914_){
_start:
{
switch(lean_obj_tag(v_n_913_))
{
case 0:
{
lean_object* v___x_915_; 
v___x_915_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_915_;
}
case 1:
{
lean_object* v_pre_916_; lean_object* v_str_917_; uint8_t v___x_918_; 
v_pre_916_ = lean_ctor_get(v_n_913_, 0);
v_str_917_ = lean_ctor_get(v_n_913_, 1);
v___x_918_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_916_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_919_ = 1;
v___x_920_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_921_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_913_, v___x_919_);
v___x_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_920_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_inc_ref(v_str_917_);
lean_inc(v_pre_916_);
lean_dec_ref_known(v_n_913_, 2);
v___x_924_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_925_ = lean_unsigned_to_nat(1024u);
v___x_926_ = l_Lean_Name_reprPrec(v_pre_916_, v___x_925_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_924_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_String_quote(v_str_917_);
v___x_931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Repr_addAppParen(v___x_932_, v_prec_914_);
return v___x_933_;
}
}
default: 
{
lean_object* v_pre_934_; lean_object* v_i_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_pre_934_ = lean_ctor_get(v_n_913_, 0);
lean_inc(v_pre_934_);
v_i_935_ = lean_ctor_get(v_n_913_, 1);
lean_inc(v_i_935_);
lean_dec_ref_known(v_n_913_, 2);
v___x_936_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_937_ = lean_unsigned_to_nat(1024u);
v___x_938_ = l_Lean_Name_reprPrec(v_pre_934_, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_936_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Nat_reprFast(v_i_935_);
v___x_943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_941_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Repr_addAppParen(v___x_944_, v_prec_914_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_946_, lean_object* v_prec_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Name_reprPrec(v_n_946_, v_prec_947_);
lean_dec(v_prec_947_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 1)
{
lean_object* v_pre_952_; lean_object* v_str_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_pre_952_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_pre_952_);
v_str_953_ = lean_ctor_get(v_x_951_, 1);
lean_inc_ref(v_str_953_);
lean_dec_ref_known(v_x_951_, 2);
v___x_954_ = lean_string_capitalize(v_str_953_);
v___x_955_ = l_Lean_Name_str___override(v_pre_952_, v___x_954_);
return v___x_955_;
}
else
{
return v_x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
switch(lean_obj_tag(v_x_956_))
{
case 0:
{
if (lean_obj_tag(v_x_957_) == 0)
{
lean_inc(v_x_958_);
return v_x_958_;
}
else
{
return v_x_956_;
}
}
case 1:
{
lean_object* v_pre_959_; lean_object* v_str_960_; uint8_t v___x_961_; 
v_pre_959_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_pre_959_);
v_str_960_ = lean_ctor_get(v_x_956_, 1);
lean_inc_ref(v_str_960_);
v___x_961_ = lean_name_eq(v_x_956_, v_x_957_);
lean_dec_ref_known(v_x_956_, 2);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l_Lean_Name_replacePrefix(v_pre_959_, v_x_957_, v_x_958_);
v___x_963_ = l_Lean_Name_str___override(v___x_962_, v_str_960_);
return v___x_963_;
}
else
{
lean_dec_ref(v_str_960_);
lean_dec(v_pre_959_);
lean_inc(v_x_958_);
return v_x_958_;
}
}
default: 
{
lean_object* v_pre_964_; lean_object* v_i_965_; uint8_t v___x_966_; 
v_pre_964_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_pre_964_);
v_i_965_ = lean_ctor_get(v_x_956_, 1);
lean_inc(v_i_965_);
v___x_966_ = lean_name_eq(v_x_956_, v_x_957_);
lean_dec_ref_known(v_x_956_, 2);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = l_Lean_Name_replacePrefix(v_pre_964_, v_x_957_, v_x_958_);
v___x_968_ = l_Lean_Name_num___override(v___x_967_, v_i_965_);
return v___x_968_;
}
else
{
lean_dec(v_i_965_);
lean_dec(v_pre_964_);
lean_inc(v_x_958_);
return v_x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Name_replacePrefix(v_x_969_, v_x_970_, v_x_971_);
lean_dec(v_x_971_);
lean_dec(v_x_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_973_, lean_object* v_x_974_){
_start:
{
switch(lean_obj_tag(v_x_974_))
{
case 0:
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_x_973_);
return v___x_975_;
}
case 1:
{
if (lean_obj_tag(v_x_973_) == 1)
{
lean_object* v_pre_976_; lean_object* v_str_977_; lean_object* v_pre_978_; lean_object* v_str_979_; uint8_t v___x_980_; 
v_pre_976_ = lean_ctor_get(v_x_974_, 0);
v_str_977_ = lean_ctor_get(v_x_974_, 1);
v_pre_978_ = lean_ctor_get(v_x_973_, 0);
lean_inc(v_pre_978_);
v_str_979_ = lean_ctor_get(v_x_973_, 1);
lean_inc_ref(v_str_979_);
lean_dec_ref_known(v_x_973_, 2);
v___x_980_ = lean_string_dec_eq(v_str_979_, v_str_977_);
lean_dec_ref(v_str_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec(v_pre_978_);
v___x_981_ = lean_box(0);
return v___x_981_;
}
else
{
v_x_973_ = v_pre_978_;
v_x_974_ = v_pre_976_;
goto _start;
}
}
else
{
lean_object* v___x_983_; 
lean_dec(v_x_973_);
v___x_983_ = lean_box(0);
return v___x_983_;
}
}
default: 
{
if (lean_obj_tag(v_x_973_) == 2)
{
lean_object* v_pre_984_; lean_object* v_i_985_; lean_object* v_pre_986_; lean_object* v_i_987_; uint8_t v___x_988_; 
v_pre_984_ = lean_ctor_get(v_x_974_, 0);
v_i_985_ = lean_ctor_get(v_x_974_, 1);
v_pre_986_ = lean_ctor_get(v_x_973_, 0);
lean_inc(v_pre_986_);
v_i_987_ = lean_ctor_get(v_x_973_, 1);
lean_inc(v_i_987_);
lean_dec_ref_known(v_x_973_, 2);
v___x_988_ = lean_nat_dec_eq(v_i_987_, v_i_985_);
lean_dec(v_i_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec(v_pre_986_);
v___x_989_ = lean_box(0);
return v___x_989_;
}
else
{
v_x_973_ = v_pre_986_;
v_x_974_ = v_pre_984_;
goto _start;
}
}
else
{
lean_object* v___x_991_; 
lean_dec(v_x_973_);
v___x_991_ = lean_box(0);
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Name_eraseSuffix_x3f(v_x_992_, v_x_993_);
lean_dec(v_x_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_995_, lean_object* v_f_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_Name_hasMacroScopes(v_n_995_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
v___x_998_ = lean_apply_1(v_f_996_, v_n_995_);
return v___x_998_;
}
else
{
lean_object* v_view_999_; lean_object* v_name_1000_; lean_object* v_imported_1001_; lean_object* v_ctx_1002_; lean_object* v_scopes_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1012_; 
v_view_999_ = l_Lean_extractMacroScopes(v_n_995_);
v_name_1000_ = lean_ctor_get(v_view_999_, 0);
v_imported_1001_ = lean_ctor_get(v_view_999_, 1);
v_ctx_1002_ = lean_ctor_get(v_view_999_, 2);
v_scopes_1003_ = lean_ctor_get(v_view_999_, 3);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_view_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1005_ = v_view_999_;
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_scopes_1003_);
lean_inc(v_ctx_1002_);
lean_inc(v_imported_1001_);
lean_inc(v_name_1000_);
lean_dec(v_view_999_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_apply_1(v_f_996_, v_name_1000_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_imported_1001_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_ctx_1002_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_scopes_1003_);
v___x_1009_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_MacroScopesView_review(v___x_1009_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1013_, lean_object* v_x_1014_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 1)
{
lean_object* v_pre_1015_; lean_object* v_str_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_pre_1015_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_pre_1015_);
v_str_1016_ = lean_ctor_get(v_x_1014_, 1);
lean_inc_ref(v_str_1016_);
lean_dec_ref_known(v_x_1014_, 2);
v___x_1017_ = lean_string_append(v_str_1016_, v_suffix_1013_);
lean_dec_ref(v_suffix_1013_);
v___x_1018_ = l_Lean_Name_str___override(v_pre_1015_, v___x_1017_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Name_str___override(v_x_1014_, v_suffix_1013_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1020_, lean_object* v_suffix_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = l_Lean_Name_hasMacroScopes(v_n_1020_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1021_, v_n_1020_);
return v___x_1023_;
}
else
{
lean_object* v_view_1024_; lean_object* v_name_1025_; lean_object* v_imported_1026_; lean_object* v_ctx_1027_; lean_object* v_scopes_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1037_; 
v_view_1024_ = l_Lean_extractMacroScopes(v_n_1020_);
v_name_1025_ = lean_ctor_get(v_view_1024_, 0);
v_imported_1026_ = lean_ctor_get(v_view_1024_, 1);
v_ctx_1027_ = lean_ctor_get(v_view_1024_, 2);
v_scopes_1028_ = lean_ctor_get(v_view_1024_, 3);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_view_1024_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1030_ = v_view_1024_;
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_scopes_1028_);
lean_inc(v_ctx_1027_);
lean_inc(v_imported_1026_);
lean_inc(v_name_1025_);
lean_dec(v_view_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1021_, v_name_1025_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_imported_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_ctx_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_scopes_1028_);
v___x_1034_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_MacroScopesView_review(v___x_1034_);
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1038_, lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 1)
{
lean_object* v_pre_1040_; lean_object* v_str_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_pre_1040_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_pre_1040_);
v_str_1041_ = lean_ctor_get(v_x_1039_, 1);
lean_inc_ref(v_str_1041_);
lean_dec_ref_known(v_x_1039_, 2);
v___x_1042_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1043_ = lean_string_append(v_str_1041_, v___x_1042_);
v___x_1044_ = l_Nat_reprFast(v_idx_1038_);
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_Name_str___override(v_pre_1040_, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1047_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1048_ = l_Nat_reprFast(v_idx_1038_);
v___x_1049_ = lean_string_append(v___x_1047_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = l_Lean_Name_str___override(v_x_1039_, v___x_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1051_, lean_object* v_idx_1052_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Name_hasMacroScopes(v_n_1051_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1052_, v_n_1051_);
return v___x_1054_;
}
else
{
lean_object* v_view_1055_; lean_object* v_name_1056_; lean_object* v_imported_1057_; lean_object* v_ctx_1058_; lean_object* v_scopes_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1068_; 
v_view_1055_ = l_Lean_extractMacroScopes(v_n_1051_);
v_name_1056_ = lean_ctor_get(v_view_1055_, 0);
v_imported_1057_ = lean_ctor_get(v_view_1055_, 1);
v_ctx_1058_ = lean_ctor_get(v_view_1055_, 2);
v_scopes_1059_ = lean_ctor_get(v_view_1055_, 3);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_view_1055_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1061_ = v_view_1055_;
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_scopes_1059_);
lean_inc(v_ctx_1058_);
lean_inc(v_imported_1057_);
lean_inc(v_name_1056_);
lean_dec(v_view_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1052_, v_name_1056_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_imported_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_ctx_1058_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_scopes_1059_);
v___x_1065_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_MacroScopesView_review(v___x_1065_);
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1069_, lean_object* v_x_1070_){
_start:
{
switch(lean_obj_tag(v_x_1070_))
{
case 0:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Name_str___override(v_x_1070_, v_pre_1069_);
return v___x_1071_;
}
case 1:
{
lean_object* v_pre_1072_; lean_object* v_str_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_pre_1072_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_pre_1072_);
v_str_1073_ = lean_ctor_get(v_x_1070_, 1);
lean_inc_ref(v_str_1073_);
lean_dec_ref_known(v_x_1070_, 2);
v___x_1074_ = lean_string_append(v_pre_1069_, v_str_1073_);
lean_dec_ref(v_str_1073_);
v___x_1075_ = l_Lean_Name_str___override(v_pre_1072_, v___x_1074_);
return v___x_1075_;
}
default: 
{
lean_object* v_pre_1076_; lean_object* v_i_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_pre_1076_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_pre_1076_);
v_i_1077_ = lean_ctor_get(v_x_1070_, 1);
lean_inc(v_i_1077_);
lean_dec_ref_known(v_x_1070_, 2);
v___x_1078_ = l_Lean_Name_str___override(v_pre_1076_, v_pre_1069_);
v___x_1079_ = l_Lean_Name_num___override(v___x_1078_, v_i_1077_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore(lean_object* v_n_1080_, lean_object* v_pre_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_Name_hasMacroScopes(v_n_1080_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Name_appendBefore___lam__0(v_pre_1081_, v_n_1080_);
return v___x_1083_;
}
else
{
lean_object* v_view_1084_; lean_object* v_name_1085_; lean_object* v_imported_1086_; lean_object* v_ctx_1087_; lean_object* v_scopes_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1097_; 
v_view_1084_ = l_Lean_extractMacroScopes(v_n_1080_);
v_name_1085_ = lean_ctor_get(v_view_1084_, 0);
v_imported_1086_ = lean_ctor_get(v_view_1084_, 1);
v_ctx_1087_ = lean_ctor_get(v_view_1084_, 2);
v_scopes_1088_ = lean_ctor_get(v_view_1084_, 3);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_view_1084_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1090_ = v_view_1084_;
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_scopes_1088_);
lean_inc(v_ctx_1087_);
lean_inc(v_imported_1086_);
lean_inc(v_name_1085_);
lean_dec(v_view_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = l_Lean_Name_appendBefore___lam__0(v_pre_1081_, v_name_1085_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_imported_1086_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_ctx_1087_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_scopes_1088_);
v___x_1094_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_MacroScopesView_review(v___x_1094_);
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_h__1_1100_, lean_object* v_h__2_1101_, lean_object* v_h__3_1102_, lean_object* v_h__4_1103_){
_start:
{
switch(lean_obj_tag(v_x_1098_))
{
case 0:
{
lean_dec(v_h__3_1102_);
lean_dec(v_h__2_1101_);
if (lean_obj_tag(v_x_1099_) == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_h__4_1103_);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_apply_1(v_h__1_1100_, v___x_1104_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_h__1_1100_);
v___x_1106_ = lean_apply_5(v_h__4_1103_, v_x_1098_, v_x_1099_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1106_;
}
}
case 1:
{
lean_dec(v_h__3_1102_);
lean_dec(v_h__1_1100_);
if (lean_obj_tag(v_x_1099_) == 1)
{
lean_object* v_pre_1107_; lean_object* v_str_1108_; lean_object* v_pre_1109_; lean_object* v_str_1110_; lean_object* v___x_1111_; 
lean_dec(v_h__4_1103_);
v_pre_1107_ = lean_ctor_get(v_x_1098_, 0);
lean_inc(v_pre_1107_);
v_str_1108_ = lean_ctor_get(v_x_1098_, 1);
lean_inc_ref(v_str_1108_);
lean_dec_ref_known(v_x_1098_, 2);
v_pre_1109_ = lean_ctor_get(v_x_1099_, 0);
lean_inc(v_pre_1109_);
v_str_1110_ = lean_ctor_get(v_x_1099_, 1);
lean_inc_ref(v_str_1110_);
lean_dec_ref_known(v_x_1099_, 2);
v___x_1111_ = lean_apply_4(v_h__2_1101_, v_pre_1107_, v_str_1108_, v_pre_1109_, v_str_1110_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; 
lean_dec(v_h__2_1101_);
v___x_1112_ = lean_apply_5(v_h__4_1103_, v_x_1098_, v_x_1099_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1112_;
}
}
default: 
{
lean_dec(v_h__2_1101_);
lean_dec(v_h__1_1100_);
if (lean_obj_tag(v_x_1099_) == 2)
{
lean_object* v_pre_1113_; lean_object* v_i_1114_; lean_object* v_pre_1115_; lean_object* v_i_1116_; lean_object* v___x_1117_; 
lean_dec(v_h__4_1103_);
v_pre_1113_ = lean_ctor_get(v_x_1098_, 0);
lean_inc(v_pre_1113_);
v_i_1114_ = lean_ctor_get(v_x_1098_, 1);
lean_inc(v_i_1114_);
lean_dec_ref_known(v_x_1098_, 2);
v_pre_1115_ = lean_ctor_get(v_x_1099_, 0);
lean_inc(v_pre_1115_);
v_i_1116_ = lean_ctor_get(v_x_1099_, 1);
lean_inc(v_i_1116_);
lean_dec_ref_known(v_x_1099_, 2);
v___x_1117_ = lean_apply_4(v_h__3_1102_, v_pre_1113_, v_i_1114_, v_pre_1115_, v_i_1116_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; 
lean_dec(v_h__3_1102_);
v___x_1118_ = lean_apply_5(v_h__4_1103_, v_x_1098_, v_x_1099_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_h__1_1122_, lean_object* v_h__2_1123_, lean_object* v_h__3_1124_, lean_object* v_h__4_1125_){
_start:
{
switch(lean_obj_tag(v_x_1120_))
{
case 0:
{
lean_dec(v_h__3_1124_);
lean_dec(v_h__2_1123_);
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_h__4_1125_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_apply_1(v_h__1_1122_, v___x_1126_);
return v___x_1127_;
}
else
{
lean_object* v___x_1128_; 
lean_dec(v_h__1_1122_);
v___x_1128_ = lean_apply_5(v_h__4_1125_, v_x_1120_, v_x_1121_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1128_;
}
}
case 1:
{
lean_dec(v_h__3_1124_);
lean_dec(v_h__1_1122_);
if (lean_obj_tag(v_x_1121_) == 1)
{
lean_object* v_pre_1129_; lean_object* v_str_1130_; lean_object* v_pre_1131_; lean_object* v_str_1132_; lean_object* v___x_1133_; 
lean_dec(v_h__4_1125_);
v_pre_1129_ = lean_ctor_get(v_x_1120_, 0);
lean_inc(v_pre_1129_);
v_str_1130_ = lean_ctor_get(v_x_1120_, 1);
lean_inc_ref(v_str_1130_);
lean_dec_ref_known(v_x_1120_, 2);
v_pre_1131_ = lean_ctor_get(v_x_1121_, 0);
lean_inc(v_pre_1131_);
v_str_1132_ = lean_ctor_get(v_x_1121_, 1);
lean_inc_ref(v_str_1132_);
lean_dec_ref_known(v_x_1121_, 2);
v___x_1133_ = lean_apply_4(v_h__2_1123_, v_pre_1129_, v_str_1130_, v_pre_1131_, v_str_1132_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
lean_dec(v_h__2_1123_);
v___x_1134_ = lean_apply_5(v_h__4_1125_, v_x_1120_, v_x_1121_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1134_;
}
}
default: 
{
lean_dec(v_h__2_1123_);
lean_dec(v_h__1_1122_);
if (lean_obj_tag(v_x_1121_) == 2)
{
lean_object* v_pre_1135_; lean_object* v_i_1136_; lean_object* v_pre_1137_; lean_object* v_i_1138_; lean_object* v___x_1139_; 
lean_dec(v_h__4_1125_);
v_pre_1135_ = lean_ctor_get(v_x_1120_, 0);
lean_inc(v_pre_1135_);
v_i_1136_ = lean_ctor_get(v_x_1120_, 1);
lean_inc(v_i_1136_);
lean_dec_ref_known(v_x_1120_, 2);
v_pre_1137_ = lean_ctor_get(v_x_1121_, 0);
lean_inc(v_pre_1137_);
v_i_1138_ = lean_ctor_get(v_x_1121_, 1);
lean_inc(v_i_1138_);
lean_dec_ref_known(v_x_1121_, 2);
v___x_1139_ = lean_apply_4(v_h__3_1124_, v_pre_1135_, v_i_1136_, v_pre_1137_, v_i_1138_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; 
lean_dec(v_h__3_1124_);
v___x_1140_ = lean_apply_5(v_h__4_1125_, v_x_1120_, v_x_1121_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1141_, lean_object* v_b_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_name_eq(v_a_1141_, v_b_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1144_, lean_object* v_b_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_Lean_Name_instDecidableEq(v_a_1144_, v_b_1145_);
lean_dec(v_b_1145_);
lean_dec(v_a_1144_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1148_){
_start:
{
lean_object* v_namePrefix_1149_; lean_object* v_idx_1150_; lean_object* v___x_1151_; 
v_namePrefix_1149_ = lean_ctor_get(v_g_1148_, 0);
lean_inc(v_namePrefix_1149_);
v_idx_1150_ = lean_ctor_get(v_g_1148_, 1);
lean_inc(v_idx_1150_);
lean_dec_ref(v_g_1148_);
v___x_1151_ = l_Lean_Name_num___override(v_namePrefix_1149_, v_idx_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1152_){
_start:
{
lean_object* v_namePrefix_1153_; lean_object* v_idx_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
v_namePrefix_1153_ = lean_ctor_get(v_g_1152_, 0);
v_idx_1154_ = lean_ctor_get(v_g_1152_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_g_1152_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1156_ = v_g_1152_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_idx_1154_);
lean_inc(v_namePrefix_1153_);
lean_dec(v_g_1152_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_idx_1154_, v___x_1158_);
lean_dec(v_idx_1154_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_namePrefix_1153_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1164_){
_start:
{
lean_object* v_namePrefix_1165_; lean_object* v_idx_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1178_; 
v_namePrefix_1165_ = lean_ctor_get(v_g_1164_, 0);
v_idx_1166_ = lean_ctor_get(v_g_1164_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_g_1164_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1168_ = v_g_1164_;
v_isShared_1169_ = v_isSharedCheck_1178_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_idx_1166_);
lean_inc(v_namePrefix_1165_);
lean_dec(v_g_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1178_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_inc(v_idx_1166_);
lean_inc(v_namePrefix_1165_);
v___x_1170_ = l_Lean_Name_num___override(v_namePrefix_1165_, v_idx_1166_);
v___x_1171_ = lean_unsigned_to_nat(1u);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1171_);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_nat_add(v_idx_1166_, v___x_1171_);
lean_dec(v_idx_1166_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_namePrefix_1165_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1179_, lean_object* v_r_1180_, lean_object* v_____r_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_apply_2(v_toPure_1179_, lean_box(0), v_r_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1183_, lean_object* v_setNGen_1184_, lean_object* v_toBind_1185_, lean_object* v_ngen_1186_){
_start:
{
lean_object* v_namePrefix_1187_; lean_object* v_idx_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1201_; 
v_namePrefix_1187_ = lean_ctor_get(v_ngen_1186_, 0);
v_idx_1188_ = lean_ctor_get(v_ngen_1186_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_ngen_1186_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1190_ = v_ngen_1186_;
v_isShared_1191_ = v_isSharedCheck_1201_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_idx_1188_);
lean_inc(v_namePrefix_1187_);
lean_dec(v_ngen_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1201_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_r_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
lean_inc(v_idx_1188_);
lean_inc(v_namePrefix_1187_);
v_r_1192_ = l_Lean_Name_num___override(v_namePrefix_1187_, v_idx_1188_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1193_, 0, v_toPure_1183_);
lean_closure_set(v___f_1193_, 1, v_r_1192_);
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_idx_1188_, v___x_1194_);
lean_dec(v_idx_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1195_);
v___x_1197_ = v___x_1190_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_namePrefix_1187_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_apply_1(v_setNGen_1184_, v___x_1197_);
v___x_1199_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v___x_1198_, v___f_1193_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1202_, lean_object* v_inst_1203_){
_start:
{
lean_object* v_toApplicative_1204_; lean_object* v_toBind_1205_; lean_object* v_getNGen_1206_; lean_object* v_setNGen_1207_; lean_object* v_toPure_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; 
v_toApplicative_1204_ = lean_ctor_get(v_inst_1202_, 0);
lean_inc_ref(v_toApplicative_1204_);
v_toBind_1205_ = lean_ctor_get(v_inst_1202_, 1);
lean_inc_n(v_toBind_1205_, 2);
lean_dec_ref(v_inst_1202_);
v_getNGen_1206_ = lean_ctor_get(v_inst_1203_, 0);
lean_inc(v_getNGen_1206_);
v_setNGen_1207_ = lean_ctor_get(v_inst_1203_, 1);
lean_inc(v_setNGen_1207_);
lean_dec_ref(v_inst_1203_);
v_toPure_1208_ = lean_ctor_get(v_toApplicative_1204_, 1);
lean_inc(v_toPure_1208_);
lean_dec_ref(v_toApplicative_1204_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1209_, 0, v_toPure_1208_);
lean_closure_set(v___f_1209_, 1, v_setNGen_1207_);
lean_closure_set(v___f_1209_, 2, v_toBind_1205_);
v___x_1210_ = lean_apply_4(v_toBind_1205_, lean_box(0), lean_box(0), v_getNGen_1206_, v___f_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_mkFreshId___redArg(v_inst_1212_, v_inst_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1215_, lean_object* v_inst_1216_, lean_object* v_ngen_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_apply_1(v_setNGen_1215_, v_ngen_1217_);
v___x_1219_ = lean_apply_2(v_inst_1216_, lean_box(0), v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v_getNGen_1222_; lean_object* v_setNGen_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1232_; 
v_getNGen_1222_ = lean_ctor_get(v_inst_1221_, 0);
v_setNGen_1223_ = lean_ctor_get(v_inst_1221_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_inst_1221_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1225_ = v_inst_1221_;
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_setNGen_1223_);
lean_inc(v_getNGen_1222_);
lean_dec(v_inst_1221_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_inc(v_inst_1220_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1227_, 0, v_setNGen_1223_);
lean_closure_set(v___f_1227_, 1, v_inst_1220_);
v___x_1228_ = lean_apply_2(v_inst_1220_, lean_box(0), v_getNGen_1222_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v___f_1227_);
lean_ctor_set(v___x_1225_, 0, v___x_1228_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___f_1227_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1233_, lean_object* v_n_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1235_, v_inst_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_dec(v_x_1238_);
return v_x_1239_;
}
else
{
lean_object* v_head_1241_; lean_object* v_tail_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1253_; 
v_head_1241_ = lean_ctor_get(v_x_1240_, 0);
v_tail_1242_ = lean_ctor_get(v_x_1240_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1244_ = v_x_1240_;
v_isShared_1245_ = v_isSharedCheck_1253_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_tail_1242_);
lean_inc(v_head_1241_);
lean_dec(v_x_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1253_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
lean_inc(v_x_1238_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 5);
lean_ctor_set(v___x_1244_, 1, v_x_1238_);
lean_ctor_set(v___x_1244_, 0, v_x_1239_);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_x_1239_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_x_1238_);
v___x_1247_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = l_String_quote(v_head_1241_);
v___x_1249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1247_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v_x_1239_ = v___x_1250_;
v_x_1240_ = v_tail_1242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_dec(v_x_1254_);
return v_x_1255_;
}
else
{
lean_object* v_head_1257_; lean_object* v_tail_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1269_; 
v_head_1257_ = lean_ctor_get(v_x_1256_, 0);
v_tail_1258_ = lean_ctor_get(v_x_1256_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1260_ = v_x_1256_;
v_isShared_1261_ = v_isSharedCheck_1269_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_tail_1258_);
lean_inc(v_head_1257_);
lean_dec(v_x_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1269_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
lean_inc(v_x_1254_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 5);
lean_ctor_set(v___x_1260_, 1, v_x_1254_);
lean_ctor_set(v___x_1260_, 0, v_x_1255_);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_x_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_x_1254_);
v___x_1263_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1264_ = l_String_quote(v_head_1257_);
v___x_1265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1263_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1254_, v___x_1266_, v_tail_1258_);
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_String_quote(v___y_1270_);
v___x_1272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
if (lean_obj_tag(v_x_1273_) == 0)
{
lean_object* v___x_1275_; 
lean_dec(v_x_1274_);
v___x_1275_ = lean_box(0);
return v___x_1275_;
}
else
{
lean_object* v_tail_1276_; 
v_tail_1276_ = lean_ctor_get(v_x_1273_, 1);
if (lean_obj_tag(v_tail_1276_) == 0)
{
lean_object* v_head_1277_; lean_object* v___x_1278_; 
lean_dec(v_x_1274_);
v_head_1277_ = lean_ctor_get(v_x_1273_, 0);
lean_inc(v_head_1277_);
lean_dec_ref_known(v_x_1273_, 2);
v___x_1278_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1277_);
return v___x_1278_;
}
else
{
lean_object* v_head_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_inc(v_tail_1276_);
v_head_1279_ = lean_ctor_get(v_x_1273_, 0);
lean_inc(v_head_1279_);
lean_dec_ref_known(v_x_1273_, 2);
v___x_1280_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1279_);
v___x_1281_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1274_, v___x_1280_, v_tail_1276_);
return v___x_1281_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1294_ = lean_string_length(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1296_ = lean_nat_to_int(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1301_){
_start:
{
if (lean_obj_tag(v_a_1301_) == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1303_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1304_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1301_, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1306_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1304_);
v___x_1308_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1305_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Std_Format_fill(v___x_1310_);
return v___x_1311_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_unsigned_to_nat(2u);
v___x_1319_ = lean_nat_to_int(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_to_int(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1328_, lean_object* v_prec_1329_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 0)
{
lean_object* v_ns_1330_; lean_object* v___y_1332_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_ns_1330_ = lean_ctor_get(v_x_1328_, 0);
lean_inc(v_ns_1330_);
lean_dec_ref_known(v_x_1328_, 1);
v___x_1341_ = lean_unsigned_to_nat(1024u);
v___x_1342_ = lean_nat_dec_le(v___x_1341_, v_prec_1329_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1332_ = v___x_1343_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1332_ = v___x_1344_;
goto v___jp_1331_;
}
v___jp_1331_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1333_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1334_ = lean_unsigned_to_nat(1024u);
v___x_1335_ = l_Lean_Name_reprPrec(v_ns_1330_, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1333_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
lean_inc(v___y_1332_);
v___x_1337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___y_1332_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = 0;
v___x_1339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*1, v___x_1338_);
v___x_1340_ = l_Repr_addAppParen(v___x_1339_, v_prec_1329_);
return v___x_1340_;
}
}
else
{
lean_object* v_n_1345_; lean_object* v_fields_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1370_; 
v_n_1345_ = lean_ctor_get(v_x_1328_, 0);
v_fields_1346_ = lean_ctor_get(v_x_1328_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_x_1328_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1348_ = v_x_1328_;
v_isShared_1349_ = v_isSharedCheck_1370_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_fields_1346_);
lean_inc(v_n_1345_);
lean_dec(v_x_1328_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1370_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___y_1351_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_unsigned_to_nat(1024u);
v___x_1367_ = lean_nat_dec_le(v___x_1366_, v_prec_1329_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1351_ = v___x_1368_;
goto v___jp_1350_;
}
else
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1351_ = v___x_1369_;
goto v___jp_1350_;
}
v___jp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1352_ = lean_box(1);
v___x_1353_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1354_ = lean_unsigned_to_nat(1024u);
v___x_1355_ = l_Lean_Name_reprPrec(v_n_1345_, v___x_1354_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 5);
lean_ctor_set(v___x_1348_, 1, v___x_1355_);
lean_ctor_set(v___x_1348_, 0, v___x_1353_);
v___x_1357_ = v___x_1348_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1352_);
v___x_1359_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1346_);
v___x_1360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
lean_inc(v___y_1351_);
v___x_1361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1351_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = 0;
v___x_1363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*1, v___x_1362_);
v___x_1364_ = l_Repr_addAppParen(v___x_1363_, v_prec_1329_);
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1371_, lean_object* v_prec_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1371_, v_prec_1372_);
lean_dec(v_prec_1372_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_nat_to_int(v_a_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1376_, lean_object* v_n_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1379_, lean_object* v_n_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1379_, v_n_1380_);
lean_dec(v_n_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1384_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_dec(v_x_1387_);
return v_x_1388_;
}
else
{
lean_object* v_head_1390_; lean_object* v_tail_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1402_; 
v_head_1390_ = lean_ctor_get(v_x_1389_, 0);
v_tail_1391_ = lean_ctor_get(v_x_1389_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1393_ = v_x_1389_;
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_tail_1391_);
lean_inc(v_head_1390_);
lean_dec(v_x_1389_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
lean_inc(v_x_1387_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 5);
lean_ctor_set(v___x_1393_, 1, v_x_1387_);
lean_ctor_set(v___x_1393_, 0, v_x_1388_);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_x_1388_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_x_1387_);
v___x_1396_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1390_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1396_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v_x_1388_ = v___x_1399_;
v_x_1389_ = v_tail_1391_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
if (lean_obj_tag(v_x_1405_) == 0)
{
lean_dec(v_x_1403_);
return v_x_1404_;
}
else
{
lean_object* v_head_1406_; lean_object* v_tail_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1418_; 
v_head_1406_ = lean_ctor_get(v_x_1405_, 0);
v_tail_1407_ = lean_ctor_get(v_x_1405_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1405_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1409_ = v_x_1405_;
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_tail_1407_);
lean_inc(v_head_1406_);
lean_dec(v_x_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
lean_inc(v_x_1403_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 5);
lean_ctor_set(v___x_1409_, 1, v_x_1403_);
lean_ctor_set(v___x_1409_, 0, v_x_1404_);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_x_1404_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_x_1403_);
v___x_1412_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1406_, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1412_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1403_, v___x_1415_, v_tail_1407_);
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
if (lean_obj_tag(v_x_1419_) == 0)
{
lean_object* v___x_1421_; 
lean_dec(v_x_1420_);
v___x_1421_ = lean_box(0);
return v___x_1421_;
}
else
{
lean_object* v_tail_1422_; 
v_tail_1422_ = lean_ctor_get(v_x_1419_, 1);
if (lean_obj_tag(v_tail_1422_) == 0)
{
lean_object* v_head_1423_; lean_object* v___x_1424_; 
lean_dec(v_x_1420_);
v_head_1423_ = lean_ctor_get(v_x_1419_, 0);
lean_inc(v_head_1423_);
lean_dec_ref_known(v_x_1419_, 2);
v___x_1424_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1423_);
return v___x_1424_;
}
else
{
lean_object* v_head_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_inc(v_tail_1422_);
v_head_1425_ = lean_ctor_get(v_x_1419_, 0);
lean_inc(v_head_1425_);
lean_dec_ref_known(v_x_1419_, 2);
v___x_1426_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1425_);
v___x_1427_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1420_, v___x_1426_, v_tail_1422_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1428_){
_start:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1430_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1431_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1428_, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1433_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1431_);
v___x_1435_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1432_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = 0;
v___x_1439_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*1, v___x_1438_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
if (lean_obj_tag(v_x_1451_) == 0)
{
lean_dec(v_x_1449_);
return v_x_1450_;
}
else
{
lean_object* v_head_1452_; lean_object* v_tail_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1464_; 
v_head_1452_ = lean_ctor_get(v_x_1451_, 0);
v_tail_1453_ = lean_ctor_get(v_x_1451_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_1451_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1455_ = v_x_1451_;
v_isShared_1456_ = v_isSharedCheck_1464_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_tail_1453_);
lean_inc(v_head_1452_);
lean_dec(v_x_1451_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1464_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
lean_inc(v_x_1449_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 5);
lean_ctor_set(v___x_1455_, 1, v_x_1449_);
lean_ctor_set(v___x_1455_, 0, v_x_1450_);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_x_1450_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_x_1449_);
v___x_1458_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = l_Lean_Syntax_instRepr_repr(v_head_1452_, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v_x_1450_ = v___x_1461_;
v_x_1451_ = v_tail_1453_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_dec(v_x_1465_);
return v_x_1466_;
}
else
{
lean_object* v_head_1468_; lean_object* v_tail_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1480_; 
v_head_1468_ = lean_ctor_get(v_x_1467_, 0);
v_tail_1469_ = lean_ctor_get(v_x_1467_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_x_1467_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1471_ = v_x_1467_;
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_tail_1469_);
lean_inc(v_head_1468_);
lean_dec(v_x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
lean_inc(v_x_1465_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 5);
lean_ctor_set(v___x_1471_, 1, v_x_1465_);
lean_ctor_set(v___x_1471_, 0, v_x_1466_);
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_x_1466_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_x_1465_);
v___x_1474_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = l_Lean_Syntax_instRepr_repr(v_head_1468_, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1474_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1465_, v___x_1477_, v_tail_1469_);
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v___x_1483_; 
lean_dec(v_x_1482_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
else
{
lean_object* v_tail_1484_; 
v_tail_1484_ = lean_ctor_get(v_x_1481_, 1);
if (lean_obj_tag(v_tail_1484_) == 0)
{
lean_object* v_head_1485_; lean_object* v___x_1486_; 
lean_dec(v_x_1482_);
v_head_1485_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_head_1485_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1486_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1485_);
return v___x_1486_;
}
else
{
lean_object* v_head_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_inc(v_tail_1484_);
v_head_1487_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_head_1487_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1488_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1487_);
v___x_1489_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1482_, v___x_1488_, v_tail_1484_);
return v___x_1489_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1492_ = lean_string_length(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1494_ = lean_nat_to_int(v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = lean_array_get_size(v_xs_1500_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_nat_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1504_ = lean_array_to_list(v_xs_1500_);
v___x_1505_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1506_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1508_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1506_);
v___x_1510_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1507_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Std_Format_fill(v___x_1512_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; 
lean_dec_ref(v_xs_1500_);
v___x_1514_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1528_, lean_object* v_prec_1529_){
_start:
{
lean_object* v___y_1531_; 
switch(lean_obj_tag(v_x_1528_))
{
case 0:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = lean_unsigned_to_nat(1024u);
v___x_1538_ = lean_nat_dec_le(v___x_1537_, v_prec_1529_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1531_ = v___x_1539_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1531_ = v___x_1540_;
goto v___jp_1530_;
}
}
case 1:
{
lean_object* v_info_1541_; lean_object* v_kind_1542_; lean_object* v_args_1543_; lean_object* v___y_1545_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_info_1541_ = lean_ctor_get(v_x_1528_, 0);
lean_inc(v_info_1541_);
v_kind_1542_ = lean_ctor_get(v_x_1528_, 1);
lean_inc(v_kind_1542_);
v_args_1543_ = lean_ctor_get(v_x_1528_, 2);
lean_inc_ref(v_args_1543_);
lean_dec_ref_known(v_x_1528_, 3);
v___x_1561_ = lean_unsigned_to_nat(1024u);
v___x_1562_ = lean_nat_dec_le(v___x_1561_, v_prec_1529_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1545_ = v___x_1563_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1545_ = v___x_1564_;
goto v___jp_1544_;
}
v___jp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1546_ = lean_box(1);
v___x_1547_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1548_ = lean_unsigned_to_nat(1024u);
v___x_1549_ = l_instReprSourceInfo_repr(v_info_1541_, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1546_);
v___x_1552_ = l_Lean_Name_reprPrec(v_kind_1542_, v___x_1548_);
v___x_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1546_);
v___x_1555_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1543_);
v___x_1556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
lean_inc(v___y_1545_);
v___x_1557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___y_1545_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = 0;
v___x_1559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*1, v___x_1558_);
v___x_1560_ = l_Repr_addAppParen(v___x_1559_, v_prec_1529_);
return v___x_1560_;
}
}
case 2:
{
lean_object* v_info_1565_; lean_object* v_val_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1591_; 
v_info_1565_ = lean_ctor_get(v_x_1528_, 0);
v_val_1566_ = lean_ctor_get(v_x_1528_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1528_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1568_ = v_x_1528_;
v_isShared_1569_ = v_isSharedCheck_1591_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_val_1566_);
lean_inc(v_info_1565_);
lean_dec(v_x_1528_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1591_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___y_1571_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = lean_unsigned_to_nat(1024u);
v___x_1588_ = lean_nat_dec_le(v___x_1587_, v_prec_1529_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1571_ = v___x_1589_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1571_ = v___x_1590_;
goto v___jp_1570_;
}
v___jp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1572_ = lean_box(1);
v___x_1573_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1574_ = lean_unsigned_to_nat(1024u);
v___x_1575_ = l_instReprSourceInfo_repr(v_info_1565_, v___x_1574_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 5);
lean_ctor_set(v___x_1568_, 1, v___x_1575_);
lean_ctor_set(v___x_1568_, 0, v___x_1573_);
v___x_1577_ = v___x_1568_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___x_1572_);
v___x_1579_ = l_String_quote(v_val_1566_);
v___x_1580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1578_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_inc(v___y_1571_);
v___x_1582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___y_1571_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = 0;
v___x_1584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*1, v___x_1583_);
v___x_1585_ = l_Repr_addAppParen(v___x_1584_, v_prec_1529_);
return v___x_1585_;
}
}
}
}
default: 
{
lean_object* v_info_1592_; lean_object* v_rawVal_1593_; lean_object* v_val_1594_; lean_object* v_preresolved_1595_; lean_object* v___y_1597_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_info_1592_ = lean_ctor_get(v_x_1528_, 0);
lean_inc(v_info_1592_);
v_rawVal_1593_ = lean_ctor_get(v_x_1528_, 1);
lean_inc_ref(v_rawVal_1593_);
v_val_1594_ = lean_ctor_get(v_x_1528_, 2);
lean_inc(v_val_1594_);
v_preresolved_1595_ = lean_ctor_get(v_x_1528_, 3);
lean_inc(v_preresolved_1595_);
lean_dec_ref_known(v_x_1528_, 4);
v___x_1620_ = lean_unsigned_to_nat(1024u);
v___x_1621_ = lean_nat_dec_le(v___x_1620_, v_prec_1529_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1597_ = v___x_1622_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1597_ = v___x_1623_;
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1598_ = lean_box(1);
v___x_1599_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1600_ = lean_unsigned_to_nat(1024u);
v___x_1601_ = l_instReprSourceInfo_repr(v_info_1592_, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1599_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v___x_1598_);
v___x_1604_ = lean_substring_tostring(v_rawVal_1593_);
v___x_1605_ = l_String_quote(v___x_1604_);
v___x_1606_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1607_ = lean_string_append(v___x_1605_, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1603_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1598_);
v___x_1611_ = l_Lean_Name_reprPrec(v_val_1594_, v___x_1600_);
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1598_);
v___x_1614_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1595_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
lean_inc(v___y_1597_);
v___x_1616_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___y_1597_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = 0;
v___x_1618_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*1, v___x_1617_);
v___x_1619_ = l_Repr_addAppParen(v___x_1618_, v_prec_1529_);
return v___x_1619_;
}
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1532_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1531_);
v___x_1533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___y_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = 0;
v___x_1535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*1, v___x_1534_);
v___x_1536_ = l_Repr_addAppParen(v___x_1535_, v_prec_1529_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = l_Lean_Syntax_instRepr_repr(v___y_1624_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1627_, lean_object* v_prec_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Syntax_instRepr_repr(v_x_1627_, v_prec_1628_);
lean_dec(v_prec_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1630_, lean_object* v_n_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1633_, lean_object* v_n_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1633_, v_n_1634_);
lean_dec(v_n_1634_);
return v_res_1635_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(7u);
v___x_1652_ = lean_nat_to_int(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1655_ = lean_string_length(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1657_ = lean_nat_to_int(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1663_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1664_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = l_Lean_Syntax_instRepr_repr(v_x_1662_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = 0;
v___x_1669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1663_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1672_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v___x_1670_);
v___x_1674_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1671_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*1, v___x_1668_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1678_, lean_object* v_x_1679_, lean_object* v_prec_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1682_, lean_object* v_x_1683_, lean_object* v_prec_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1682_, v_x_1683_, v_prec_1684_);
lean_dec(v_prec_1684_);
lean_dec(v_ks_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1687_, 0, v_ks_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1688_){
_start:
{
lean_inc(v_stx_1688_);
return v_stx_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1689_);
lean_dec(v_stx_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1693_; 
v___f_1693_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1696_, lean_object* v_ks_1697_){
_start:
{
lean_object* v___f_1698_; 
v___f_1698_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1699_, lean_object* v_ks_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1699_, v_ks_1700_);
lean_dec(v_ks_1700_);
lean_dec(v_k_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1703_; 
v___f_1703_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1706_, lean_object* v_k_x27_1707_){
_start:
{
lean_object* v___f_1708_; 
v___f_1708_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1709_, lean_object* v_k_x27_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1709_, v_k_x27_1710_);
lean_dec(v_k_x27_1710_);
lean_dec(v_ks_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1712_){
_start:
{
lean_inc(v_s_1712_);
return v_s_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1713_);
lean_dec(v_s_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1717_, lean_object* v_ss_1718_, lean_object* v_n_1719_, lean_object* v_res_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1721_, 0, v_info_1717_);
lean_ctor_set(v___x_1721_, 1, v_ss_1718_);
lean_ctor_set(v___x_1721_, 2, v_n_1719_);
lean_ctor_set(v___x_1721_, 3, v_res_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1731_; 
v___f_1731_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1734_){
_start:
{
lean_object* v___f_1735_; 
v___f_1735_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1736_);
lean_dec(v_k_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1739_, 0, v_k_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1740_, lean_object* v_x_1741_){
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
v___x_1749_ = lean_string_dec_eq(v_head_1745_, v_head_1747_);
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
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
uint8_t v_res_1753_; lean_object* v_r_1754_; 
v_res_1753_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1751_, v_x_1752_);
lean_dec(v_x_1752_);
lean_dec(v_x_1751_);
v_r_1754_ = lean_box(v_res_1753_);
return v_r_1754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_object* v_ns_1757_; lean_object* v_ns_1758_; uint8_t v___x_1759_; 
v_ns_1757_ = lean_ctor_get(v_x_1755_, 0);
v_ns_1758_ = lean_ctor_get(v_x_1756_, 0);
v___x_1759_ = lean_name_eq(v_ns_1757_, v_ns_1758_);
return v___x_1759_;
}
else
{
uint8_t v___x_1760_; 
v___x_1760_ = 0;
return v___x_1760_;
}
}
else
{
if (lean_obj_tag(v_x_1756_) == 1)
{
lean_object* v_n_1761_; lean_object* v_fields_1762_; lean_object* v_n_1763_; lean_object* v_fields_1764_; uint8_t v___x_1765_; 
v_n_1761_ = lean_ctor_get(v_x_1755_, 0);
v_fields_1762_ = lean_ctor_get(v_x_1755_, 1);
v_n_1763_ = lean_ctor_get(v_x_1756_, 0);
v_fields_1764_ = lean_ctor_get(v_x_1756_, 1);
v___x_1765_ = lean_name_eq(v_n_1761_, v_n_1763_);
if (v___x_1765_ == 0)
{
return v___x_1765_;
}
else
{
uint8_t v___x_1766_; 
v___x_1766_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1762_, v_fields_1764_);
return v___x_1766_;
}
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
uint8_t v_res_1770_; lean_object* v_r_1771_; 
v_res_1770_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1768_, v_x_1769_);
lean_dec_ref(v_x_1769_);
lean_dec_ref(v_x_1768_);
v_r_1771_ = lean_box(v_res_1770_);
return v_r_1771_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1774_, lean_object* v_x_1775_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
if (lean_obj_tag(v_x_1775_) == 0)
{
uint8_t v___x_1776_; 
v___x_1776_ = 1;
return v___x_1776_;
}
else
{
uint8_t v___x_1777_; 
v___x_1777_ = 0;
return v___x_1777_;
}
}
else
{
if (lean_obj_tag(v_x_1775_) == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
else
{
lean_object* v_head_1779_; lean_object* v_tail_1780_; lean_object* v_head_1781_; lean_object* v_tail_1782_; uint8_t v___x_1783_; 
v_head_1779_ = lean_ctor_get(v_x_1774_, 0);
v_tail_1780_ = lean_ctor_get(v_x_1774_, 1);
v_head_1781_ = lean_ctor_get(v_x_1775_, 0);
v_tail_1782_ = lean_ctor_get(v_x_1775_, 1);
v___x_1783_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1779_, v_head_1781_);
if (v___x_1783_ == 0)
{
return v___x_1783_;
}
else
{
v_x_1774_ = v_tail_1780_;
v_x_1775_ = v_tail_1782_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
uint8_t v_res_1787_; lean_object* v_r_1788_; 
v_res_1787_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1785_, v_x_1786_);
lean_dec(v_x_1786_);
lean_dec(v_x_1785_);
v_r_1788_ = lean_box(v_res_1787_);
return v_r_1788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
switch(lean_obj_tag(v_x_1789_))
{
case 0:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 1;
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1790_) == 1)
{
lean_object* v_kind_1793_; lean_object* v_args_1794_; lean_object* v_kind_1795_; lean_object* v_args_1796_; uint8_t v___x_1797_; 
v_kind_1793_ = lean_ctor_get(v_x_1789_, 1);
v_args_1794_ = lean_ctor_get(v_x_1789_, 2);
v_kind_1795_ = lean_ctor_get(v_x_1790_, 1);
v_args_1796_ = lean_ctor_get(v_x_1790_, 2);
v___x_1797_ = lean_name_eq(v_kind_1793_, v_kind_1795_);
if (v___x_1797_ == 0)
{
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_array_get_size(v_args_1794_);
v___x_1799_ = lean_array_get_size(v_args_1796_);
v___x_1800_ = lean_nat_dec_eq(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
return v___x_1800_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1794_, v_args_1796_, v___x_1798_);
return v___x_1801_;
}
}
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1790_) == 2)
{
lean_object* v_val_1803_; lean_object* v_val_1804_; uint8_t v___x_1805_; 
v_val_1803_ = lean_ctor_get(v_x_1789_, 1);
v_val_1804_ = lean_ctor_get(v_x_1790_, 1);
v___x_1805_ = lean_string_dec_eq(v_val_1803_, v_val_1804_);
return v___x_1805_;
}
else
{
uint8_t v___x_1806_; 
v___x_1806_ = 0;
return v___x_1806_;
}
}
default: 
{
if (lean_obj_tag(v_x_1790_) == 3)
{
lean_object* v_rawVal_1807_; lean_object* v_val_1808_; lean_object* v_preresolved_1809_; lean_object* v_rawVal_1810_; lean_object* v_val_1811_; lean_object* v_preresolved_1812_; uint8_t v___y_1814_; uint8_t v___x_1816_; 
v_rawVal_1807_ = lean_ctor_get(v_x_1789_, 1);
v_val_1808_ = lean_ctor_get(v_x_1789_, 2);
v_preresolved_1809_ = lean_ctor_get(v_x_1789_, 3);
v_rawVal_1810_ = lean_ctor_get(v_x_1790_, 1);
v_val_1811_ = lean_ctor_get(v_x_1790_, 2);
v_preresolved_1812_ = lean_ctor_get(v_x_1790_, 3);
lean_inc_ref(v_rawVal_1810_);
lean_inc_ref(v_rawVal_1807_);
v___x_1816_ = lean_substring_beq(v_rawVal_1807_, v_rawVal_1810_);
if (v___x_1816_ == 0)
{
v___y_1814_ = v___x_1816_;
goto v___jp_1813_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_name_eq(v_val_1808_, v_val_1811_);
v___y_1814_ = v___x_1817_;
goto v___jp_1813_;
}
v___jp_1813_:
{
if (v___y_1814_ == 0)
{
return v___y_1814_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1809_, v_preresolved_1812_);
return v___x_1815_;
}
}
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = 0;
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1819_, lean_object* v_ys_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_zero_1822_; uint8_t v_isZero_1823_; 
v_zero_1822_ = lean_unsigned_to_nat(0u);
v_isZero_1823_ = lean_nat_dec_eq(v_x_1821_, v_zero_1822_);
if (v_isZero_1823_ == 1)
{
lean_dec(v_x_1821_);
return v_isZero_1823_;
}
else
{
lean_object* v_one_1824_; lean_object* v_n_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_one_1824_ = lean_unsigned_to_nat(1u);
v_n_1825_ = lean_nat_sub(v_x_1821_, v_one_1824_);
lean_dec(v_x_1821_);
v___x_1826_ = lean_array_fget_borrowed(v_xs_1819_, v_n_1825_);
v___x_1827_ = lean_array_fget_borrowed(v_ys_1820_, v_n_1825_);
v___x_1828_ = l_Lean_Syntax_structEq(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec(v_n_1825_);
return v___x_1828_;
}
else
{
v_x_1821_ = v_n_1825_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1830_, lean_object* v_ys_1831_, lean_object* v_x_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1830_, v_ys_1831_, v_x_1832_);
lean_dec_ref(v_ys_1831_);
lean_dec_ref(v_xs_1830_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_Lean_Syntax_structEq(v_x_1835_, v_x_1836_);
lean_dec(v_x_1836_);
lean_dec(v_x_1835_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1839_, lean_object* v_ys_1840_, lean_object* v_hsz_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1839_, v_ys_1840_, v_x_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1845_, lean_object* v_ys_1846_, lean_object* v_hsz_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1845_, v_ys_1846_, v_hsz_1847_, v_x_1848_, v_x_1849_);
lean_dec_ref(v_ys_1846_);
lean_dec_ref(v_xs_1845_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1856_; 
v___f_1856_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1859_){
_start:
{
lean_object* v___f_1860_; 
v___f_1860_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Syntax_instBEqTSyntax(v_k_1861_);
lean_dec(v_k_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1863_, lean_object* v_i_1864_){
_start:
{
lean_object* v_zero_1865_; uint8_t v_isZero_1866_; 
v_zero_1865_ = lean_unsigned_to_nat(0u);
v_isZero_1866_ = lean_nat_dec_eq(v_i_1864_, v_zero_1865_);
if (v_isZero_1866_ == 1)
{
lean_object* v___x_1867_; 
lean_dec(v_i_1864_);
v___x_1867_ = lean_box(0);
return v___x_1867_;
}
else
{
lean_object* v_one_1868_; lean_object* v_n_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_one_1868_ = lean_unsigned_to_nat(1u);
v_n_1869_ = lean_nat_sub(v_i_1864_, v_one_1868_);
lean_dec(v_i_1864_);
v___x_1870_ = lean_array_fget_borrowed(v_as_1863_, v_n_1869_);
v___x_1871_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
v_i_1864_ = v_n_1869_;
goto _start;
}
else
{
lean_dec(v_n_1869_);
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1873_){
_start:
{
switch(lean_obj_tag(v_x_1873_))
{
case 2:
{
lean_object* v_info_1874_; lean_object* v___x_1875_; 
v_info_1874_ = lean_ctor_get(v_x_1873_, 0);
lean_inc(v_info_1874_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_info_1874_);
return v___x_1875_;
}
case 3:
{
lean_object* v_info_1876_; lean_object* v___x_1877_; 
v_info_1876_ = lean_ctor_get(v_x_1873_, 0);
lean_inc(v_info_1876_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_info_1876_);
return v___x_1877_;
}
case 1:
{
lean_object* v_info_1878_; 
v_info_1878_ = lean_ctor_get(v_x_1873_, 0);
if (lean_obj_tag(v_info_1878_) == 2)
{
lean_object* v_args_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_args_1879_ = lean_ctor_get(v_x_1873_, 2);
v___x_1880_ = lean_array_get_size(v_args_1879_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1879_, v___x_1880_);
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; 
lean_inc(v_info_1878_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_info_1878_);
return v___x_1882_;
}
}
default: 
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_box(0);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1884_);
lean_dec(v_x_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1886_, lean_object* v_i_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1886_, v_i_1887_);
lean_dec_ref(v_as_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1889_, lean_object* v_i_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1889_, v_i_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1893_, lean_object* v_i_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1893_, v_i_1894_, v_a_1895_);
lean_dec_ref(v_as_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_box(2);
return v___x_1899_;
}
else
{
lean_object* v_val_1900_; 
v_val_1900_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v___x_1898_, 1);
return v_val_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Syntax_getTailInfo(v_stx_1901_);
lean_dec(v_stx_1901_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1903_);
if (lean_obj_tag(v___x_1904_) == 1)
{
lean_object* v_val_1905_; 
v_val_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_val_1905_);
lean_dec_ref_known(v___x_1904_, 1);
if (lean_obj_tag(v_val_1905_) == 0)
{
lean_object* v_trailing_1906_; lean_object* v_startPos_1907_; lean_object* v_stopPos_1908_; lean_object* v___x_1909_; 
v_trailing_1906_ = lean_ctor_get(v_val_1905_, 2);
lean_inc_ref(v_trailing_1906_);
lean_dec_ref_known(v_val_1905_, 4);
v_startPos_1907_ = lean_ctor_get(v_trailing_1906_, 1);
lean_inc(v_startPos_1907_);
v_stopPos_1908_ = lean_ctor_get(v_trailing_1906_, 2);
lean_inc(v_stopPos_1908_);
lean_dec_ref(v_trailing_1906_);
v___x_1909_ = lean_nat_sub(v_stopPos_1908_, v_startPos_1907_);
lean_dec(v_startPos_1907_);
lean_dec(v_stopPos_1908_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
lean_dec(v_val_1905_);
v___x_1910_ = lean_unsigned_to_nat(0u);
return v___x_1910_;
}
}
else
{
lean_object* v___x_1911_; 
lean_dec(v___x_1904_);
v___x_1911_ = lean_unsigned_to_nat(0u);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Syntax_getTrailingSize(v_stx_1912_);
lean_dec(v_stx_1912_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = l_Lean_Syntax_getTailInfo(v_stx_1914_);
v___x_1916_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1915_);
lean_dec(v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1917_);
lean_dec(v_stx_1917_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1919_, uint8_t v_canonicalOnly_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = l_Lean_Syntax_getTailInfo(v_stx_1919_);
v___x_1922_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1921_, v_canonicalOnly_1920_);
lean_dec(v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1923_, lean_object* v_canonicalOnly_1924_){
_start:
{
uint8_t v_canonicalOnly_boxed_1925_; lean_object* v_res_1926_; 
v_canonicalOnly_boxed_1925_ = lean_unbox(v_canonicalOnly_1924_);
v_res_1926_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1923_, v_canonicalOnly_boxed_1925_);
lean_dec(v_stx_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1927_, uint8_t v_withLeading_1928_, uint8_t v_withTrailing_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Syntax_getHeadInfo(v_stx_1927_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_leading_1931_; lean_object* v_pos_1932_; lean_object* v___x_1933_; 
v_leading_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_leading_1931_);
v_pos_1932_ = lean_ctor_get(v___x_1930_, 1);
lean_inc(v_pos_1932_);
lean_dec_ref_known(v___x_1930_, 4);
v___x_1933_ = l_Lean_Syntax_getTailInfo(v_stx_1927_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_trailing_1934_; lean_object* v_endPos_1935_; lean_object* v_str_1936_; lean_object* v_startPos_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1951_; 
v_trailing_1934_ = lean_ctor_get(v___x_1933_, 2);
lean_inc_ref(v_trailing_1934_);
v_endPos_1935_ = lean_ctor_get(v___x_1933_, 3);
lean_inc(v_endPos_1935_);
lean_dec_ref_known(v___x_1933_, 4);
v_str_1936_ = lean_ctor_get(v_leading_1931_, 0);
v_startPos_1937_ = lean_ctor_get(v_leading_1931_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_leading_1931_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_leading_1931_, 2);
lean_dec(v_unused_1952_);
v___x_1939_ = v_leading_1931_;
v_isShared_1940_ = v_isSharedCheck_1951_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_startPos_1937_);
lean_inc(v_str_1936_);
lean_dec(v_leading_1931_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1951_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1949_; 
if (v_withLeading_1928_ == 0)
{
lean_dec(v_startPos_1937_);
v___y_1949_ = v_pos_1932_;
goto v___jp_1948_;
}
else
{
lean_dec(v_pos_1932_);
v___y_1949_ = v_startPos_1937_;
goto v___jp_1948_;
}
v___jp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 2, v___y_1943_);
lean_ctor_set(v___x_1939_, 1, v___y_1942_);
v___x_1945_ = v___x_1939_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_str_1936_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___y_1942_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v___y_1943_);
v___x_1945_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
return v___x_1946_;
}
}
v___jp_1948_:
{
if (v_withTrailing_1929_ == 0)
{
lean_dec_ref(v_trailing_1934_);
v___y_1942_ = v___y_1949_;
v___y_1943_ = v_endPos_1935_;
goto v___jp_1941_;
}
else
{
lean_object* v_stopPos_1950_; 
lean_dec(v_endPos_1935_);
v_stopPos_1950_ = lean_ctor_get(v_trailing_1934_, 2);
lean_inc(v_stopPos_1950_);
lean_dec_ref(v_trailing_1934_);
v___y_1942_ = v___y_1949_;
v___y_1943_ = v_stopPos_1950_;
goto v___jp_1941_;
}
}
}
}
else
{
lean_object* v___x_1953_; 
lean_dec(v___x_1933_);
lean_dec(v_pos_1932_);
lean_dec_ref(v_leading_1931_);
v___x_1953_ = lean_box(0);
return v___x_1953_;
}
}
else
{
lean_object* v___x_1954_; 
lean_dec(v___x_1930_);
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1955_, lean_object* v_withLeading_1956_, lean_object* v_withTrailing_1957_){
_start:
{
uint8_t v_withLeading_boxed_1958_; uint8_t v_withTrailing_boxed_1959_; lean_object* v_res_1960_; 
v_withLeading_boxed_1958_ = lean_unbox(v_withLeading_1956_);
v_withTrailing_boxed_1959_ = lean_unbox(v_withTrailing_1957_);
v_res_1960_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1955_, v_withLeading_boxed_1958_, v_withTrailing_boxed_1959_);
lean_dec(v_stx_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1961_, lean_object* v_f_1962_, lean_object* v_i_1963_){
_start:
{
lean_object* v_zero_1964_; uint8_t v_isZero_1965_; 
v_zero_1964_ = lean_unsigned_to_nat(0u);
v_isZero_1965_ = lean_nat_dec_eq(v_i_1963_, v_zero_1964_);
if (v_isZero_1965_ == 1)
{
lean_object* v___x_1966_; 
lean_dec(v_i_1963_);
lean_dec_ref(v_f_1962_);
lean_dec_ref(v_a_1961_);
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
else
{
lean_object* v_one_1967_; lean_object* v_n_1968_; lean_object* v_v_1969_; lean_object* v___x_1970_; 
v_one_1967_ = lean_unsigned_to_nat(1u);
v_n_1968_ = lean_nat_sub(v_i_1963_, v_one_1967_);
lean_dec(v_i_1963_);
v_v_1969_ = lean_array_fget_borrowed(v_a_1961_, v_n_1968_);
lean_inc_ref(v_f_1962_);
lean_inc(v_v_1969_);
v___x_1970_ = lean_apply_1(v_f_1962_, v_v_1969_);
if (lean_obj_tag(v___x_1970_) == 0)
{
v_i_1963_ = v_n_1968_;
goto _start;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_f_1962_);
v_val_1972_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v___x_1970_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_array_fset(v_a_1961_, v_n_1968_, v_val_1972_);
lean_dec(v_n_1968_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1981_, lean_object* v_a_1982_, lean_object* v_f_1983_, lean_object* v_i_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1982_, v_f_1983_, v_i_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1986_, lean_object* v_x_1987_){
_start:
{
switch(lean_obj_tag(v_x_1987_))
{
case 2:
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_val_1988_ = lean_ctor_get(v_x_1987_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v_x_1987_, 0);
lean_dec(v_unused_1997_);
v___x_1990_ = v_x_1987_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v_x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v_info_1986_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_info_1986_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_val_1988_);
v___x_1993_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
}
case 3:
{
lean_object* v_rawVal_1998_; lean_object* v_val_1999_; lean_object* v_preresolved_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
v_rawVal_1998_ = lean_ctor_get(v_x_1987_, 1);
v_val_1999_ = lean_ctor_get(v_x_1987_, 2);
v_preresolved_2000_ = lean_ctor_get(v_x_1987_, 3);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v_x_1987_, 0);
lean_dec(v_unused_2009_);
v___x_2002_ = v_x_1987_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_preresolved_2000_);
lean_inc(v_val_1999_);
lean_inc(v_rawVal_1998_);
lean_dec(v_x_1987_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_info_1986_);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_info_1986_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_rawVal_1998_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_val_1999_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_preresolved_2000_);
v___x_2005_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
}
}
case 1:
{
lean_object* v_info_2010_; lean_object* v_kind_2011_; lean_object* v_args_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2030_; 
v_info_2010_ = lean_ctor_get(v_x_1987_, 0);
v_kind_2011_ = lean_ctor_get(v_x_1987_, 1);
v_args_2012_ = lean_ctor_get(v_x_1987_, 2);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2014_ = v_x_1987_;
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_args_2012_);
lean_inc(v_kind_2011_);
lean_inc(v_info_2010_);
lean_dec(v_x_1987_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_array_get_size(v_args_2012_);
v___x_2017_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1986_, v_args_2012_, v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; 
lean_del_object(v___x_2014_);
lean_dec(v_kind_2011_);
lean_dec(v_info_2010_);
v___x_2018_ = lean_box(0);
return v___x_2018_;
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2029_; 
v_val_2019_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2021_ = v___x_2017_;
v_isShared_2022_ = v_isSharedCheck_2029_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v___x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2029_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 2, v_val_2019_);
v___x_2024_ = v___x_2014_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_info_2010_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_kind_2011_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_val_2019_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2031_; 
lean_dec(v_x_1987_);
lean_dec(v_info_1986_);
v___x_2031_ = lean_box(0);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2032_, lean_object* v_a_2033_, lean_object* v_i_2034_){
_start:
{
lean_object* v_zero_2035_; uint8_t v_isZero_2036_; 
v_zero_2035_ = lean_unsigned_to_nat(0u);
v_isZero_2036_ = lean_nat_dec_eq(v_i_2034_, v_zero_2035_);
if (v_isZero_2036_ == 1)
{
lean_object* v___x_2037_; 
lean_dec(v_i_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_info_2032_);
v___x_2037_ = lean_box(0);
return v___x_2037_;
}
else
{
lean_object* v_one_2038_; lean_object* v_n_2039_; lean_object* v_v_2040_; lean_object* v___x_2041_; 
v_one_2038_ = lean_unsigned_to_nat(1u);
v_n_2039_ = lean_nat_sub(v_i_2034_, v_one_2038_);
lean_dec(v_i_2034_);
v_v_2040_ = lean_array_fget_borrowed(v_a_2033_, v_n_2039_);
lean_inc(v_v_2040_);
lean_inc(v_info_2032_);
v___x_2041_ = l_Lean_Syntax_setTailInfoAux(v_info_2032_, v_v_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
v_i_2034_ = v_n_2039_;
goto _start;
}
else
{
lean_object* v_val_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_info_2032_);
v_val_2043_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2045_ = v___x_2041_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_val_2043_);
lean_dec(v___x_2041_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_array_fset(v_a_2033_, v_n_2039_, v_val_2043_);
lean_dec(v_n_2039_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2052_, lean_object* v_info_2053_){
_start:
{
lean_object* v___x_2054_; 
lean_inc(v_stx_2052_);
v___x_2054_ = l_Lean_Syntax_setTailInfoAux(v_info_2053_, v_stx_2052_);
if (lean_obj_tag(v___x_2054_) == 0)
{
return v_stx_2052_;
}
else
{
lean_object* v_val_2055_; 
lean_dec(v_stx_2052_);
v_val_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_val_2055_);
lean_dec_ref_known(v___x_2054_, 1);
return v_val_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_Syntax_getTailInfo(v_stx_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_trailing_2058_; lean_object* v_leading_2059_; lean_object* v_pos_2060_; lean_object* v_endPos_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2079_; 
v_trailing_2058_ = lean_ctor_get(v___x_2057_, 2);
v_leading_2059_ = lean_ctor_get(v___x_2057_, 0);
v_pos_2060_ = lean_ctor_get(v___x_2057_, 1);
v_endPos_2061_ = lean_ctor_get(v___x_2057_, 3);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2063_ = v___x_2057_;
v_isShared_2064_ = v_isSharedCheck_2079_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_endPos_2061_);
lean_inc(v_trailing_2058_);
lean_inc(v_pos_2060_);
lean_inc(v_leading_2059_);
lean_dec(v___x_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2079_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_str_2065_; lean_object* v_startPos_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2077_; 
v_str_2065_ = lean_ctor_get(v_trailing_2058_, 0);
v_startPos_2066_ = lean_ctor_get(v_trailing_2058_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_trailing_2058_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_trailing_2058_, 2);
lean_dec(v_unused_2078_);
v___x_2068_ = v_trailing_2058_;
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_startPos_2066_);
lean_inc(v_str_2065_);
lean_dec(v_trailing_2058_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
lean_inc(v_startPos_2066_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 2, v_startPos_2066_);
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_str_2065_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_startPos_2066_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_startPos_2066_);
v___x_2071_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 2, v___x_2071_);
v___x_2073_ = v___x_2063_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_leading_2059_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_pos_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_endPos_2061_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Syntax_setTailInfo(v_stx_2056_, v___x_2073_);
return v___x_2074_;
}
}
}
}
}
else
{
lean_dec(v___x_2057_);
return v_stx_2056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2080_, lean_object* v_f_2081_, lean_object* v_i_2082_){
_start:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_array_get_size(v_a_2080_);
v___x_2084_ = lean_nat_dec_lt(v_i_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v_i_2082_);
lean_dec_ref(v_f_2081_);
lean_dec_ref(v_a_2080_);
v___x_2085_ = lean_box(0);
return v___x_2085_;
}
else
{
lean_object* v_v_2086_; lean_object* v___x_2087_; 
v_v_2086_ = lean_array_fget_borrowed(v_a_2080_, v_i_2082_);
lean_inc_ref(v_f_2081_);
lean_inc(v_v_2086_);
v___x_2087_ = lean_apply_1(v_f_2081_, v_v_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_i_2082_, v___x_2088_);
lean_dec(v_i_2082_);
v_i_2082_ = v___x_2089_;
goto _start;
}
else
{
lean_object* v_val_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_f_2081_);
v_val_2091_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2093_ = v___x_2087_;
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_val_2091_);
lean_dec(v___x_2087_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_array_fset(v_a_2080_, v_i_2082_, v_val_2091_);
lean_dec(v_i_2082_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2095_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2100_, lean_object* v_inst_2101_, lean_object* v_a_2102_, lean_object* v_f_2103_, lean_object* v_i_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2102_, v_f_2103_, v_i_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_inst_2107_, lean_object* v_a_2108_, lean_object* v_f_2109_, lean_object* v_i_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2106_, v_inst_2107_, v_a_2108_, v_f_2109_, v_i_2110_);
lean_dec(v_inst_2107_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2112_, lean_object* v_x_2113_){
_start:
{
switch(lean_obj_tag(v_x_2113_))
{
case 2:
{
lean_object* v_val_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2122_; 
v_val_2114_ = lean_ctor_get(v_x_2113_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v_x_2113_, 0);
lean_dec(v_unused_2123_);
v___x_2116_ = v_x_2113_;
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_val_2114_);
lean_dec(v_x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v_info_2112_);
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_info_2112_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_val_2114_);
v___x_2119_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
case 3:
{
lean_object* v_rawVal_2124_; lean_object* v_val_2125_; lean_object* v_preresolved_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2134_; 
v_rawVal_2124_ = lean_ctor_get(v_x_2113_, 1);
v_val_2125_ = lean_ctor_get(v_x_2113_, 2);
v_preresolved_2126_ = lean_ctor_get(v_x_2113_, 3);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_x_2113_, 0);
lean_dec(v_unused_2135_);
v___x_2128_ = v_x_2113_;
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_preresolved_2126_);
lean_inc(v_val_2125_);
lean_inc(v_rawVal_2124_);
lean_dec(v_x_2113_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_info_2112_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_info_2112_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_rawVal_2124_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_val_2125_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_preresolved_2126_);
v___x_2131_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
}
}
case 1:
{
lean_object* v_info_2136_; lean_object* v_kind_2137_; lean_object* v_args_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2156_; 
v_info_2136_ = lean_ctor_get(v_x_2113_, 0);
v_kind_2137_ = lean_ctor_get(v_x_2113_, 1);
v_args_2138_ = lean_ctor_get(v_x_2113_, 2);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2140_ = v_x_2113_;
v_isShared_2141_ = v_isSharedCheck_2156_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_args_2138_);
lean_inc(v_kind_2137_);
lean_inc(v_info_2136_);
lean_dec(v_x_2113_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2156_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2112_, v_args_2138_, v___x_2142_);
if (lean_obj_tag(v___x_2143_) == 1)
{
lean_object* v_val_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2154_; 
v_val_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_val_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 2, v_val_2144_);
v___x_2149_ = v___x_2140_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_info_2136_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_kind_2137_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_val_2144_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2149_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v___x_2155_; 
lean_dec(v___x_2143_);
lean_del_object(v___x_2140_);
lean_dec(v_kind_2137_);
lean_dec(v_info_2136_);
v___x_2155_ = lean_box(0);
return v___x_2155_;
}
}
}
default: 
{
lean_object* v___x_2157_; 
lean_dec(v_x_2113_);
lean_dec(v_info_2112_);
v___x_2157_ = lean_box(0);
return v___x_2157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2158_, lean_object* v_a_2159_, lean_object* v_i_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_array_get_size(v_a_2159_);
v___x_2162_ = lean_nat_dec_lt(v_i_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec(v_i_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_info_2158_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
else
{
lean_object* v_v_2164_; lean_object* v___x_2165_; 
v_v_2164_ = lean_array_fget_borrowed(v_a_2159_, v_i_2160_);
lean_inc(v_v_2164_);
lean_inc(v_info_2158_);
v___x_2165_ = l_Lean_Syntax_setHeadInfoAux(v_info_2158_, v_v_2164_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v_i_2160_, v___x_2166_);
lean_dec(v_i_2160_);
v_i_2160_ = v___x_2167_;
goto _start;
}
else
{
lean_object* v_val_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_info_2158_);
v_val_2169_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2171_ = v___x_2165_;
v_isShared_2172_ = v_isSharedCheck_2177_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_val_2169_);
lean_dec(v___x_2165_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2177_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_array_fset(v_a_2159_, v_i_2160_, v_val_2169_);
lean_dec(v_i_2160_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2173_);
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2178_, lean_object* v_info_2179_){
_start:
{
lean_object* v___x_2180_; 
lean_inc(v_stx_2178_);
v___x_2180_ = l_Lean_Syntax_setHeadInfoAux(v_info_2179_, v_stx_2178_);
if (lean_obj_tag(v___x_2180_) == 0)
{
return v_stx_2178_;
}
else
{
lean_object* v_val_2181_; 
lean_dec(v_stx_2178_);
v_val_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2180_, 1);
return v_val_2181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2182_, lean_object* v_x_2183_){
_start:
{
switch(lean_obj_tag(v_x_2183_))
{
case 0:
{
lean_dec(v_info_2182_);
return v_x_2183_;
}
case 1:
{
lean_object* v_kind_2184_; lean_object* v_args_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_kind_2184_ = lean_ctor_get(v_x_2183_, 1);
v_args_2185_ = lean_ctor_get(v_x_2183_, 2);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2183_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v_x_2183_, 0);
lean_dec(v_unused_2193_);
v___x_2187_ = v_x_2183_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_args_2185_);
lean_inc(v_kind_2184_);
lean_dec(v_x_2183_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_info_2182_);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_info_2182_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_kind_2184_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_args_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
case 2:
{
lean_object* v_val_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_val_2194_ = lean_ctor_get(v_x_2183_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_x_2183_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v_x_2183_, 0);
lean_dec(v_unused_2202_);
v___x_2196_ = v_x_2183_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_val_2194_);
lean_dec(v_x_2183_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_info_2182_);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_info_2182_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_val_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
default: 
{
lean_object* v_rawVal_2203_; lean_object* v_val_2204_; lean_object* v_preresolved_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_rawVal_2203_ = lean_ctor_get(v_x_2183_, 1);
v_val_2204_ = lean_ctor_get(v_x_2183_, 2);
v_preresolved_2205_ = lean_ctor_get(v_x_2183_, 3);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_2183_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v_x_2183_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v_x_2183_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_preresolved_2205_);
lean_inc(v_val_2204_);
lean_inc(v_rawVal_2203_);
lean_dec(v_x_2183_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_info_2182_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_info_2182_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_rawVal_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_val_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_preresolved_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2217_){
_start:
{
switch(lean_obj_tag(v_x_2217_))
{
case 2:
{
lean_object* v_info_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; 
v_info_2218_ = lean_ctor_get(v_x_2217_, 0);
v___x_2219_ = 0;
v___x_2220_ = l_Lean_SourceInfo_getPos_x3f(v_info_2218_, v___x_2219_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref_known(v_x_2217_, 2);
v___x_2221_ = lean_box(0);
return v___x_2221_;
}
else
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2229_);
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_x_2217_);
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_x_2217_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
case 3:
{
lean_object* v_info_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; 
v_info_2230_ = lean_ctor_get(v_x_2217_, 0);
v___x_2231_ = 0;
v___x_2232_ = l_Lean_SourceInfo_getPos_x3f(v_info_2230_, v___x_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2233_; 
lean_dec_ref_known(v_x_2217_, 4);
v___x_2233_ = lean_box(0);
return v___x_2233_;
}
else
{
lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v___x_2232_, 0);
lean_dec(v_unused_2241_);
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v_x_2217_);
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_x_2217_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
case 1:
{
lean_object* v_info_2242_; 
v_info_2242_ = lean_ctor_get(v_x_2217_, 0);
if (lean_obj_tag(v_info_2242_) == 2)
{
lean_object* v_args_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; size_t v_sz_2246_; size_t v___x_2247_; lean_object* v___x_2248_; lean_object* v_fst_2249_; 
v_args_2243_ = lean_ctor_get(v_x_2217_, 2);
lean_inc_ref(v_args_2243_);
lean_dec_ref_known(v_x_2217_, 3);
v___x_2244_ = lean_box(0);
v___x_2245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2246_ = lean_array_size(v_args_2243_);
v___x_2247_ = ((size_t)0ULL);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2243_, v_sz_2246_, v___x_2247_, v___x_2245_);
lean_dec_ref(v_args_2243_);
v_fst_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_fst_2249_);
lean_dec_ref(v___x_2248_);
if (lean_obj_tag(v_fst_2249_) == 0)
{
return v___x_2244_;
}
else
{
lean_object* v_val_2250_; 
v_val_2250_ = lean_ctor_get(v_fst_2249_, 0);
lean_inc(v_val_2250_);
lean_dec_ref_known(v_fst_2249_, 1);
return v_val_2250_;
}
}
else
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_x_2217_);
return v___x_2251_;
}
}
default: 
{
lean_object* v___x_2252_; 
lean_dec(v_x_2217_);
v___x_2252_ = lean_box(0);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2253_, size_t v_sz_2254_, size_t v_i_2255_, lean_object* v_b_2256_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_lt(v_i_2255_, v_sz_2254_);
if (v___x_2257_ == 0)
{
lean_inc_ref(v_b_2256_);
return v_b_2256_;
}
else
{
lean_object* v___x_2258_; lean_object* v_a_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_box(0);
v_a_2259_ = lean_array_uget_borrowed(v_as_2253_, v_i_2255_);
lean_inc(v_a_2259_);
v___x_2260_ = l_Lean_Syntax_getHead_x3f(v_a_2259_);
if (lean_obj_tag(v___x_2260_) == 1)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2258_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; 
lean_dec(v___x_2260_);
v___x_2263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_add(v_i_2255_, v___x_2264_);
v_i_2255_ = v___x_2265_;
v_b_2256_ = v___x_2263_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2267_, lean_object* v_sz_2268_, lean_object* v_i_2269_, lean_object* v_b_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2268_);
lean_dec(v_sz_2268_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2269_);
lean_dec(v_i_2269_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2267_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2270_);
lean_dec_ref(v_b_2270_);
lean_dec_ref(v_as_2267_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2274_, lean_object* v_source_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2276_ = l_Lean_Syntax_getHeadInfo(v_source_2275_);
v___x_2277_ = l_Lean_Syntax_setHeadInfo(v_target_2274_, v___x_2276_);
v___x_2278_ = l_Lean_Syntax_getTailInfo(v_source_2275_);
v___x_2279_ = l_Lean_Syntax_setTailInfo(v___x_2277_, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2280_, lean_object* v_source_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2280_, v_source_2281_);
lean_dec(v_source_2281_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2283_){
_start:
{
uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = 0;
v___x_2285_ = l_Lean_SourceInfo_fromRef(v_stx_2283_, v___x_2284_);
v___x_2286_ = l_Lean_Syntax_setHeadInfo(v_stx_2283_, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2287_, lean_object* v_withRef_2288_, lean_object* v_x_2289_, lean_object* v_oldRef_2290_){
_start:
{
lean_object* v_ref_2291_; lean_object* v___x_2292_; 
v_ref_2291_ = l_Lean_replaceRef(v_val_2287_, v_oldRef_2290_);
v___x_2292_ = lean_apply_3(v_withRef_2288_, lean_box(0), v_ref_2291_, v_x_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2293_, lean_object* v_withRef_2294_, lean_object* v_x_2295_, lean_object* v_oldRef_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2293_, v_withRef_2294_, v_x_2295_, v_oldRef_2296_);
lean_dec(v_oldRef_2296_);
lean_dec(v_val_2293_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2298_, lean_object* v_withRef_2299_, lean_object* v_toBind_2300_, lean_object* v_getRef_2301_, lean_object* v_____do__lift_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_dec(v_getRef_2301_);
lean_dec(v_toBind_2300_);
lean_dec(v_withRef_2299_);
return v_x_2298_;
}
else
{
lean_object* v_val_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; 
v_val_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2305_, 0, v_val_2304_);
lean_closure_set(v___f_2305_, 1, v_withRef_2299_);
lean_closure_set(v___f_2305_, 2, v_x_2298_);
v___x_2306_ = lean_apply_4(v_toBind_2300_, lean_box(0), lean_box(0), v_getRef_2301_, v___f_2305_);
return v___x_2306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_x_2309_){
_start:
{
lean_object* v_toBind_2310_; lean_object* v_getRef_2311_; lean_object* v_withRef_2312_; lean_object* v___f_2313_; lean_object* v___x_2314_; 
v_toBind_2310_ = lean_ctor_get(v_inst_2307_, 1);
lean_inc_n(v_toBind_2310_, 2);
lean_dec_ref(v_inst_2307_);
v_getRef_2311_ = lean_ctor_get(v_inst_2308_, 0);
lean_inc_n(v_getRef_2311_, 2);
v_withRef_2312_ = lean_ctor_get(v_inst_2308_, 1);
lean_inc(v_withRef_2312_);
lean_dec_ref(v_inst_2308_);
v___f_2313_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2313_, 0, v_x_2309_);
lean_closure_set(v___f_2313_, 1, v_withRef_2312_);
lean_closure_set(v___f_2313_, 2, v_toBind_2310_);
lean_closure_set(v___f_2313_, 3, v_getRef_2311_);
v___x_2314_ = lean_apply_4(v_toBind_2310_, lean_box(0), lean_box(0), v_getRef_2311_, v___f_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v_toBind_2320_; lean_object* v_getRef_2321_; lean_object* v_withRef_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; 
v_toBind_2320_ = lean_ctor_get(v_inst_2316_, 1);
lean_inc_n(v_toBind_2320_, 2);
lean_dec_ref(v_inst_2316_);
v_getRef_2321_ = lean_ctor_get(v_inst_2317_, 0);
lean_inc_n(v_getRef_2321_, 2);
v_withRef_2322_ = lean_ctor_get(v_inst_2317_, 1);
lean_inc(v_withRef_2322_);
lean_dec_ref(v_inst_2317_);
v___f_2323_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2323_, 0, v_x_2319_);
lean_closure_set(v___f_2323_, 1, v_withRef_2322_);
lean_closure_set(v___f_2323_, 2, v_toBind_2320_);
lean_closure_set(v___f_2323_, 3, v_getRef_2321_);
v___x_2324_ = lean_apply_4(v_toBind_2320_, lean_box(0), lean_box(0), v_getRef_2321_, v___f_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2334_, lean_object* v_k_2335_){
_start:
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2337_ = lean_name_eq(v_k_2335_, v___x_2336_);
if (v___x_2337_ == 0)
{
return v___x_2334_;
}
else
{
uint8_t v___x_2338_; 
v___x_2338_ = 0;
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2339_, lean_object* v_k_2340_){
_start:
{
uint8_t v___x_1783__boxed_2341_; uint8_t v_res_2342_; lean_object* v_r_2343_; 
v___x_1783__boxed_2341_ = lean_unbox(v___x_2339_);
v_res_2342_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2341_, v_k_2340_);
lean_dec(v_k_2340_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2345_, lean_object* v_p_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
if (lean_obj_tag(v_stx_2345_) == 1)
{
lean_object* v_info_2349_; lean_object* v_kind_2350_; lean_object* v_args_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_info_2349_ = lean_ctor_get(v_stx_2345_, 0);
v_kind_2350_ = lean_ctor_get(v_stx_2345_, 1);
v_args_2351_ = lean_ctor_get(v_stx_2345_, 2);
lean_inc(v_kind_2350_);
v___x_2352_ = lean_apply_1(v_p_2346_, v_kind_2350_);
v___x_2353_ = lean_unbox(v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec_ref(v_a_2347_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_stx_2345_);
lean_ctor_set(v___x_2354_, 1, v_a_2348_);
return v___x_2354_;
}
else
{
lean_object* v_methods_2355_; lean_object* v_quotContext_2356_; lean_object* v_currMacroScope_2357_; lean_object* v_currRecDepth_2358_; lean_object* v_maxRecDepth_2359_; lean_object* v_ref_2360_; lean_object* v_ref_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_methods_2355_ = lean_ctor_get(v_a_2347_, 0);
lean_inc_n(v_methods_2355_, 2);
v_quotContext_2356_ = lean_ctor_get(v_a_2347_, 1);
lean_inc_n(v_quotContext_2356_, 2);
v_currMacroScope_2357_ = lean_ctor_get(v_a_2347_, 2);
lean_inc_n(v_currMacroScope_2357_, 2);
v_currRecDepth_2358_ = lean_ctor_get(v_a_2347_, 3);
lean_inc_n(v_currRecDepth_2358_, 2);
v_maxRecDepth_2359_ = lean_ctor_get(v_a_2347_, 4);
lean_inc_n(v_maxRecDepth_2359_, 2);
v_ref_2360_ = lean_ctor_get(v_a_2347_, 5);
lean_inc(v_ref_2360_);
lean_dec_ref(v_a_2347_);
v_ref_2361_ = l_Lean_replaceRef(v_stx_2345_, v_ref_2360_);
lean_dec(v_ref_2360_);
lean_inc(v_ref_2361_);
v___x_2362_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2362_, 0, v_methods_2355_);
lean_ctor_set(v___x_2362_, 1, v_quotContext_2356_);
lean_ctor_set(v___x_2362_, 2, v_currMacroScope_2357_);
lean_ctor_set(v___x_2362_, 3, v_currRecDepth_2358_);
lean_ctor_set(v___x_2362_, 4, v_maxRecDepth_2359_);
lean_ctor_set(v___x_2362_, 5, v_ref_2361_);
lean_inc_ref(v_stx_2345_);
v___x_2363_ = l_Lean_Macro_expandMacro_x3f(v_stx_2345_, v___x_2362_, v_a_2348_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
if (lean_obj_tag(v_a_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2410_; 
lean_dec_ref_known(v___x_2362_, 6);
v_a_2365_ = lean_ctor_get(v___x_2363_, 1);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v___x_2363_, 0);
lean_dec(v_unused_2411_);
v___x_2367_ = v___x_2363_;
v_isShared_2368_ = v_isSharedCheck_2410_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2410_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_nat_dec_eq(v_currRecDepth_2358_, v_maxRecDepth_2359_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2401_; 
lean_inc_ref(v_args_2351_);
lean_inc(v_kind_2350_);
lean_inc(v_info_2349_);
lean_del_object(v___x_2367_);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_stx_2345_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; 
v_unused_2402_ = lean_ctor_get(v_stx_2345_, 2);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_stx_2345_, 1);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_stx_2345_, 0);
lean_dec(v_unused_2404_);
v___x_2371_ = v_stx_2345_;
v_isShared_2372_ = v_isSharedCheck_2401_;
goto v_resetjp_2370_;
}
else
{
lean_dec(v_stx_2345_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2401_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; size_t v_sz_2376_; size_t v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_currRecDepth_2358_, v___x_2373_);
lean_dec(v_currRecDepth_2358_);
v___x_2375_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2375_, 0, v_methods_2355_);
lean_ctor_set(v___x_2375_, 1, v_quotContext_2356_);
lean_ctor_set(v___x_2375_, 2, v_currMacroScope_2357_);
lean_ctor_set(v___x_2375_, 3, v___x_2374_);
lean_ctor_set(v___x_2375_, 4, v_maxRecDepth_2359_);
lean_ctor_set(v___x_2375_, 5, v_ref_2361_);
v_sz_2376_ = lean_array_size(v_args_2351_);
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = lean_unbox(v___x_2352_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2378_, v_sz_2376_, v___x_2377_, v_args_2351_, v___x_2375_, v_a_2365_);
lean_dec_ref_known(v___x_2375_, 6);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2391_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_a_2381_ = lean_ctor_get(v___x_2379_, 1);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2383_ = v___x_2379_;
v_isShared_2384_ = v_isSharedCheck_2391_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2391_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 2, v_a_2380_);
v___x_2386_ = v___x_2371_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_info_2349_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_kind_2350_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_a_2380_);
v___x_2386_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2386_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_2381_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_del_object(v___x_2371_);
lean_dec(v_kind_2350_);
lean_dec(v_info_2349_);
v_a_2392_ = lean_ctor_get(v___x_2379_, 0);
v_a_2393_ = lean_ctor_get(v___x_2379_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2379_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_inc(v_a_2392_);
lean_dec(v___x_2379_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2392_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_dec(v_ref_2361_);
lean_dec(v_maxRecDepth_2359_);
lean_dec(v_currRecDepth_2358_);
lean_dec(v_currMacroScope_2357_);
lean_dec(v_quotContext_2356_);
lean_dec(v_methods_2355_);
v___x_2405_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_stx_2345_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2406_);
v___x_2408_ = v___x_2367_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_a_2365_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v_val_2413_; lean_object* v___f_2414_; 
lean_dec(v_ref_2361_);
lean_dec(v_maxRecDepth_2359_);
lean_dec(v_currRecDepth_2358_);
lean_dec(v_currMacroScope_2357_);
lean_dec(v_quotContext_2356_);
lean_dec(v_methods_2355_);
lean_dec_ref_known(v_stx_2345_, 3);
v_a_2412_ = lean_ctor_get(v___x_2363_, 1);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2363_, 2);
v_val_2413_ = lean_ctor_get(v_a_2364_, 0);
lean_inc(v_val_2413_);
lean_dec_ref_known(v_a_2364_, 1);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2414_, 0, v___x_2352_);
v_stx_2345_ = v_val_2413_;
v_p_2346_ = v___f_2414_;
v_a_2347_ = v___x_2362_;
v_a_2348_ = v_a_2412_;
goto _start;
}
}
else
{
lean_object* v_a_2416_; lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref_known(v___x_2362_, 6);
lean_dec(v_ref_2361_);
lean_dec(v_maxRecDepth_2359_);
lean_dec(v_currRecDepth_2358_);
lean_dec(v_currMacroScope_2357_);
lean_dec(v_quotContext_2356_);
lean_dec(v_methods_2355_);
lean_dec_ref_known(v_stx_2345_, 3);
v_a_2416_ = lean_ctor_get(v___x_2363_, 0);
v_a_2417_ = lean_ctor_get(v___x_2363_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2363_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_inc(v_a_2416_);
lean_dec(v___x_2363_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2416_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
else
{
lean_object* v___x_2425_; 
lean_dec_ref(v_a_2347_);
lean_dec_ref(v_p_2346_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_stx_2345_);
lean_ctor_set(v___x_2425_, 1, v_a_2348_);
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2426_, size_t v_sz_2427_, size_t v_i_2428_, lean_object* v_bs_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_usize_dec_lt(v_i_2428_, v_sz_2427_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_bs_2429_);
lean_ctor_set(v___x_2433_, 1, v___y_2431_);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v_v_2436_; lean_object* v___x_2437_; 
v___x_2434_ = lean_box(v___x_2426_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2435_, 0, v___x_2434_);
v_v_2436_ = lean_array_uget_borrowed(v_bs_2429_, v_i_2428_);
lean_inc_ref(v___y_2430_);
lean_inc(v_v_2436_);
v___x_2437_ = l_Lean_expandMacros(v_v_2436_, v___f_2435_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v_a_2439_; lean_object* v___x_2440_; lean_object* v_bs_x27_2441_; size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
v_a_2439_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2437_, 2);
v___x_2440_ = lean_unsigned_to_nat(0u);
v_bs_x27_2441_ = lean_array_uset(v_bs_2429_, v_i_2428_, v___x_2440_);
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2428_, v___x_2442_);
v___x_2444_ = lean_array_uset(v_bs_x27_2441_, v_i_2428_, v_a_2438_);
v_i_2428_ = v___x_2443_;
v_bs_2429_ = v___x_2444_;
v___y_2431_ = v_a_2439_;
goto _start;
}
else
{
lean_object* v_a_2446_; lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec_ref(v_bs_2429_);
v_a_2446_ = lean_ctor_get(v___x_2437_, 0);
v_a_2447_ = lean_ctor_get(v___x_2437_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2437_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_inc(v_a_2446_);
lean_dec(v___x_2437_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2446_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2455_, lean_object* v_sz_2456_, lean_object* v_i_2457_, lean_object* v_bs_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v___x_1802__boxed_2461_; size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v___x_1802__boxed_2461_ = lean_unbox(v___x_2455_);
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2456_);
lean_dec(v_sz_2456_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2457_);
lean_dec(v_i_2457_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1802__boxed_2461_, v_sz_boxed_2462_, v_i_boxed_2463_, v_bs_2458_, v___y_2459_, v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2465_, lean_object* v_val_2466_, uint8_t v_canonical_2467_){
_start:
{
lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2468_ = l_Lean_SourceInfo_fromRef(v_src_2465_, v_canonical_2467_);
v___x_2469_ = 1;
lean_inc(v_val_2466_);
v___x_2470_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2466_, v___x_2469_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = lean_string_utf8_byte_size(v___x_2470_);
v___x_2473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2470_);
lean_ctor_set(v___x_2473_, 1, v___x_2471_);
lean_ctor_set(v___x_2473_, 2, v___x_2472_);
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2468_);
lean_ctor_set(v___x_2475_, 1, v___x_2473_);
lean_ctor_set(v___x_2475_, 2, v_val_2466_);
lean_ctor_set(v___x_2475_, 3, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2476_, lean_object* v_val_2477_, lean_object* v_canonical_2478_){
_start:
{
uint8_t v_canonical_boxed_2479_; lean_object* v_res_2480_; 
v_canonical_boxed_2479_ = lean_unbox(v_canonical_2478_);
v_res_2480_ = l_Lean_mkIdentFrom(v_src_2476_, v_val_2477_, v_canonical_boxed_2479_);
lean_dec(v_src_2476_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2496_, lean_object* v_text_2497_, uint8_t v_canonical_2498_){
_start:
{
lean_object* v_info_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_body_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_info_2499_ = l_Lean_SourceInfo_fromRef(v_src_2496_, v_canonical_2498_);
v___x_2500_ = lean_box(2);
v___x_2501_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2499_, 2);
v___x_2502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_info_2499_);
lean_ctor_set(v___x_2502_, 1, v_text_2497_);
v___x_2503_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_info_2499_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(2u);
v___x_2506_ = lean_mk_empty_array_with_capacity(v___x_2505_);
lean_inc_ref(v___x_2506_);
v___x_2507_ = lean_array_push(v___x_2506_, v___x_2502_);
v___x_2508_ = lean_array_push(v___x_2507_, v___x_2504_);
v_body_2509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2509_, 0, v___x_2500_);
lean_ctor_set(v_body_2509_, 1, v___x_2501_);
lean_ctor_set(v_body_2509_, 2, v___x_2508_);
v___x_2510_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2511_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_info_2499_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_array_push(v___x_2506_, v___x_2512_);
v___x_2514_ = lean_array_push(v___x_2513_, v_body_2509_);
v___x_2515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2500_);
lean_ctor_set(v___x_2515_, 1, v___x_2510_);
lean_ctor_set(v___x_2515_, 2, v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2516_, lean_object* v_text_2517_, lean_object* v_canonical_2518_){
_start:
{
uint8_t v_canonical_boxed_2519_; lean_object* v_res_2520_; 
v_canonical_boxed_2519_ = lean_unbox(v_canonical_2518_);
v_res_2520_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2516_, v_text_2517_, v_canonical_boxed_2519_);
lean_dec(v_src_2516_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2521_){
_start:
{
lean_object* v___x_2522_; uint8_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = 0;
v___x_2524_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2522_, v_text_2521_, v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2525_, uint8_t v_canonical_2526_, lean_object* v_toPure_2527_, lean_object* v_____do__lift_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = l_Lean_mkIdentFrom(v_____do__lift_2528_, v_val_2525_, v_canonical_2526_);
v___x_2530_ = lean_apply_2(v_toPure_2527_, lean_box(0), v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2531_, lean_object* v_canonical_2532_, lean_object* v_toPure_2533_, lean_object* v_____do__lift_2534_){
_start:
{
uint8_t v_canonical_boxed_2535_; lean_object* v_res_2536_; 
v_canonical_boxed_2535_ = lean_unbox(v_canonical_2532_);
v_res_2536_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2531_, v_canonical_boxed_2535_, v_toPure_2533_, v_____do__lift_2534_);
lean_dec(v_____do__lift_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_val_2539_, uint8_t v_canonical_2540_){
_start:
{
lean_object* v_toApplicative_2541_; lean_object* v_toBind_2542_; lean_object* v_getRef_2543_; lean_object* v_toPure_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; 
v_toApplicative_2541_ = lean_ctor_get(v_inst_2537_, 0);
lean_inc_ref(v_toApplicative_2541_);
v_toBind_2542_ = lean_ctor_get(v_inst_2537_, 1);
lean_inc(v_toBind_2542_);
lean_dec_ref(v_inst_2537_);
v_getRef_2543_ = lean_ctor_get(v_inst_2538_, 0);
lean_inc(v_getRef_2543_);
lean_dec_ref(v_inst_2538_);
v_toPure_2544_ = lean_ctor_get(v_toApplicative_2541_, 1);
lean_inc(v_toPure_2544_);
lean_dec_ref(v_toApplicative_2541_);
v___x_2545_ = lean_box(v_canonical_2540_);
v___f_2546_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2546_, 0, v_val_2539_);
lean_closure_set(v___f_2546_, 1, v___x_2545_);
lean_closure_set(v___f_2546_, 2, v_toPure_2544_);
v___x_2547_ = lean_apply_4(v_toBind_2542_, lean_box(0), lean_box(0), v_getRef_2543_, v___f_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_val_2550_, lean_object* v_canonical_2551_){
_start:
{
uint8_t v_canonical_boxed_2552_; lean_object* v_res_2553_; 
v_canonical_boxed_2552_ = lean_unbox(v_canonical_2551_);
v_res_2553_ = l_Lean_mkIdentFromRef___redArg(v_inst_2548_, v_inst_2549_, v_val_2550_, v_canonical_boxed_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_val_2557_, uint8_t v_canonical_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_mkIdentFromRef___redArg(v_inst_2555_, v_inst_2556_, v_val_2557_, v_canonical_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_val_2563_, lean_object* v_canonical_2564_){
_start:
{
uint8_t v_canonical_boxed_2565_; lean_object* v_res_2566_; 
v_canonical_boxed_2565_ = lean_unbox(v_canonical_2564_);
v_res_2566_ = l_Lean_mkIdentFromRef(v_m_2560_, v_inst_2561_, v_inst_2562_, v_val_2563_, v_canonical_boxed_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2570_, lean_object* v_c_2571_, uint8_t v_canonical_2572_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v_id_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2573_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2574_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2571_);
v_id_2575_ = l_Lean_addMacroScope(v___x_2573_, v_c_2571_, v___x_2574_);
v___x_2576_ = l_Lean_SourceInfo_fromRef(v_src_2570_, v_canonical_2572_);
v___x_2577_ = 1;
lean_inc(v_id_2575_);
v___x_2578_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2575_, v___x_2577_);
v___x_2579_ = lean_string_utf8_byte_size(v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2574_);
lean_ctor_set(v___x_2580_, 2, v___x_2579_);
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_c_2571_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___x_2581_);
v___x_2584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2576_);
lean_ctor_set(v___x_2584_, 1, v___x_2580_);
lean_ctor_set(v___x_2584_, 2, v_id_2575_);
lean_ctor_set(v___x_2584_, 3, v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2585_, lean_object* v_c_2586_, lean_object* v_canonical_2587_){
_start:
{
uint8_t v_canonical_boxed_2588_; lean_object* v_res_2589_; 
v_canonical_boxed_2588_ = lean_unbox(v_canonical_2587_);
v_res_2589_ = l_Lean_mkCIdentFrom(v_src_2585_, v_c_2586_, v_canonical_boxed_2588_);
lean_dec(v_src_2585_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2590_, uint8_t v_canonical_2591_, lean_object* v_toPure_2592_, lean_object* v_____do__lift_2593_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = l_Lean_mkCIdentFrom(v_____do__lift_2593_, v_c_2590_, v_canonical_2591_);
v___x_2595_ = lean_apply_2(v_toPure_2592_, lean_box(0), v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2596_, lean_object* v_canonical_2597_, lean_object* v_toPure_2598_, lean_object* v_____do__lift_2599_){
_start:
{
uint8_t v_canonical_boxed_2600_; lean_object* v_res_2601_; 
v_canonical_boxed_2600_ = lean_unbox(v_canonical_2597_);
v_res_2601_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2596_, v_canonical_boxed_2600_, v_toPure_2598_, v_____do__lift_2599_);
lean_dec(v_____do__lift_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_c_2604_, uint8_t v_canonical_2605_){
_start:
{
lean_object* v_toApplicative_2606_; lean_object* v_toBind_2607_; lean_object* v_getRef_2608_; lean_object* v_toPure_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; 
v_toApplicative_2606_ = lean_ctor_get(v_inst_2602_, 0);
lean_inc_ref(v_toApplicative_2606_);
v_toBind_2607_ = lean_ctor_get(v_inst_2602_, 1);
lean_inc(v_toBind_2607_);
lean_dec_ref(v_inst_2602_);
v_getRef_2608_ = lean_ctor_get(v_inst_2603_, 0);
lean_inc(v_getRef_2608_);
lean_dec_ref(v_inst_2603_);
v_toPure_2609_ = lean_ctor_get(v_toApplicative_2606_, 1);
lean_inc(v_toPure_2609_);
lean_dec_ref(v_toApplicative_2606_);
v___x_2610_ = lean_box(v_canonical_2605_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2611_, 0, v_c_2604_);
lean_closure_set(v___f_2611_, 1, v___x_2610_);
lean_closure_set(v___f_2611_, 2, v_toPure_2609_);
v___x_2612_ = lean_apply_4(v_toBind_2607_, lean_box(0), lean_box(0), v_getRef_2608_, v___f_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_c_2615_, lean_object* v_canonical_2616_){
_start:
{
uint8_t v_canonical_boxed_2617_; lean_object* v_res_2618_; 
v_canonical_boxed_2617_ = lean_unbox(v_canonical_2616_);
v_res_2618_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2613_, v_inst_2614_, v_c_2615_, v_canonical_boxed_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_c_2622_, uint8_t v_canonical_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2620_, v_inst_2621_, v_c_2622_, v_canonical_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_c_2628_, lean_object* v_canonical_2629_){
_start:
{
uint8_t v_canonical_boxed_2630_; lean_object* v_res_2631_; 
v_canonical_boxed_2630_ = lean_unbox(v_canonical_2629_);
v_res_2631_ = l_Lean_mkCIdentFromRef(v_m_2625_, v_inst_2626_, v_inst_2627_, v_c_2628_, v_canonical_boxed_2630_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2632_){
_start:
{
lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_box(0);
v___x_2634_ = 0;
v___x_2635_ = l_Lean_mkCIdentFrom(v___x_2633_, v_c_2632_, v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2636_){
_start:
{
lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2637_ = lean_box(2);
v___x_2638_ = 1;
lean_inc(v_val_2636_);
v___x_2639_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2636_, v___x_2638_);
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = lean_string_utf8_byte_size(v___x_2639_);
v___x_2642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2639_);
lean_ctor_set(v___x_2642_, 1, v___x_2640_);
lean_ctor_set(v___x_2642_, 2, v___x_2641_);
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2637_);
lean_ctor_set(v___x_2644_, 1, v___x_2642_);
lean_ctor_set(v___x_2644_, 2, v_val_2636_);
lean_ctor_set(v___x_2644_, 3, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2648_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2650_ = lean_box(2);
v___x_2651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
lean_ctor_set(v___x_2651_, 1, v___x_2649_);
lean_ctor_set(v___x_2651_, 2, v_args_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2652_, lean_object* v_as_2653_, size_t v_sz_2654_, size_t v_i_2655_, lean_object* v_b_2656_){
_start:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_usize_dec_lt(v_i_2655_, v_sz_2654_);
if (v___x_2657_ == 0)
{
lean_dec(v_sep_2652_);
return v_b_2656_;
}
else
{
lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2679_; 
v_fst_2658_ = lean_ctor_get(v_b_2656_, 0);
v_snd_2659_ = lean_ctor_get(v_b_2656_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_b_2656_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2661_ = v_b_2656_;
v_isShared_2662_ = v_isSharedCheck_2679_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
lean_dec(v_b_2656_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2679_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_r_2664_; lean_object* v_i_2673_; lean_object* v_a_2674_; uint8_t v___x_2675_; 
v_i_2673_ = lean_unsigned_to_nat(0u);
v_a_2674_ = lean_array_uget_borrowed(v_as_2653_, v_i_2655_);
v___x_2675_ = lean_nat_dec_lt(v_i_2673_, v_fst_2658_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_inc(v_a_2674_);
v___x_2676_ = lean_array_push(v_snd_2659_, v_a_2674_);
v_r_2664_ = v___x_2676_;
goto v___jp_2663_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_inc(v_sep_2652_);
v___x_2677_ = lean_array_push(v_snd_2659_, v_sep_2652_);
lean_inc(v_a_2674_);
v___x_2678_ = lean_array_push(v___x_2677_, v_a_2674_);
v_r_2664_ = v___x_2678_;
goto v___jp_2663_;
}
v___jp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_fst_2658_, v___x_2665_);
lean_dec(v_fst_2658_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v_r_2664_);
lean_ctor_set(v___x_2661_, 0, v___x_2666_);
v___x_2668_ = v___x_2661_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_r_2664_);
v___x_2668_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
size_t v___x_2669_; size_t v___x_2670_; 
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_i_2655_, v___x_2669_);
v_i_2655_ = v___x_2670_;
v_b_2656_ = v___x_2668_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2680_, lean_object* v_as_2681_, lean_object* v_sz_2682_, lean_object* v_i_2683_, lean_object* v_b_2684_){
_start:
{
size_t v_sz_boxed_2685_; size_t v_i_boxed_2686_; lean_object* v_res_2687_; 
v_sz_boxed_2685_ = lean_unbox_usize(v_sz_2682_);
lean_dec(v_sz_2682_);
v_i_boxed_2686_ = lean_unbox_usize(v_i_2683_);
lean_dec(v_i_2683_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2680_, v_as_2681_, v_sz_boxed_2685_, v_i_boxed_2686_, v_b_2684_);
lean_dec_ref(v_as_2681_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2693_, lean_object* v_sep_2694_){
_start:
{
lean_object* v___x_2695_; size_t v_sz_2696_; size_t v___x_2697_; lean_object* v___x_2698_; lean_object* v_snd_2699_; 
v___x_2695_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2696_ = lean_array_size(v_as_2693_);
v___x_2697_ = ((size_t)0ULL);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2694_, v_as_2693_, v_sz_2696_, v___x_2697_, v___x_2695_);
v_snd_2699_ = lean_ctor_get(v___x_2698_, 1);
lean_inc(v_snd_2699_);
lean_dec_ref(v___x_2698_);
return v_snd_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2700_, lean_object* v_sep_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_mkSepArray(v_as_2700_, v_sep_2701_);
lean_dec_ref(v_as_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2710_){
_start:
{
if (lean_obj_tag(v_arg_2710_) == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2711_;
}
else
{
lean_object* v_val_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_val_2712_ = lean_ctor_get(v_arg_2710_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v_arg_2710_, 1);
v___x_2713_ = lean_unsigned_to_nat(1u);
v___x_2714_ = lean_mk_empty_array_with_capacity(v___x_2713_);
v___x_2715_ = lean_array_push(v___x_2714_, v_val_2712_);
v___x_2716_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2717_ = lean_box(2);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v___x_2716_);
lean_ctor_set(v___x_2718_, 2, v___x_2715_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2725_, uint8_t v_canonical_2726_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2727_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2728_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2729_ = l_Lean_mkAtomFrom(v_ref_2725_, v___x_2728_, v_canonical_2726_);
v___x_2730_ = lean_unsigned_to_nat(1u);
v___x_2731_ = lean_mk_empty_array_with_capacity(v___x_2730_);
v___x_2732_ = lean_array_push(v___x_2731_, v___x_2729_);
v___x_2733_ = lean_box(2);
v___x_2734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
lean_ctor_set(v___x_2734_, 1, v___x_2727_);
lean_ctor_set(v___x_2734_, 2, v___x_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2735_, lean_object* v_canonical_2736_){
_start:
{
uint8_t v_canonical_boxed_2737_; lean_object* v_res_2738_; 
v_canonical_boxed_2737_ = lean_unbox(v_canonical_2736_);
v_res_2738_ = l_Lean_mkHole(v_ref_2735_, v_canonical_boxed_2737_);
lean_dec(v_ref_2735_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2739_, lean_object* v_sep_2740_){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2741_ = l_Lean_mkSepArray(v_a_2739_, v_sep_2740_);
v___x_2742_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2743_ = lean_box(2);
v___x_2744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___x_2742_);
lean_ctor_set(v___x_2744_, 2, v___x_2741_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2745_, lean_object* v_sep_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Syntax_mkSep(v_a_2745_, v_sep_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2754_, lean_object* v_elems_2755_){
_start:
{
uint8_t v___x_2756_; 
lean_inc_ref(v_sep_2754_);
v___x_2756_ = lean_string_isempty(v_sep_2754_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = l_Lean_mkAtom(v_sep_2754_);
v___x_2758_ = l_Lean_mkSepArray(v_elems_2755_, v___x_2757_);
return v___x_2758_;
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec_ref(v_sep_2754_);
v___x_2759_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2760_ = l_Lean_mkSepArray(v_elems_2755_, v___x_2759_);
return v___x_2760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2761_, lean_object* v_elems_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2761_, v_elems_2762_);
lean_dec_ref(v_elems_2762_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2764_, lean_object* v_toPure_2765_, lean_object* v_sep_2766_, lean_object* v_ref_2767_){
_start:
{
lean_object* v___y_2769_; uint8_t v___x_2772_; 
lean_inc_ref(v_sep_2766_);
v___x_2772_ = lean_string_isempty(v_sep_2766_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_mkAtomFrom(v_ref_2767_, v_sep_2766_, v___x_2772_);
v___y_2769_ = v___x_2773_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2774_; 
lean_dec_ref(v_sep_2766_);
v___x_2774_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2769_ = v___x_2774_;
goto v___jp_2768_;
}
v___jp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = l_Lean_mkSepArray(v_elems_2764_, v___y_2769_);
v___x_2771_ = lean_apply_2(v_toPure_2765_, lean_box(0), v___x_2770_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2775_, lean_object* v_toPure_2776_, lean_object* v_sep_2777_, lean_object* v_ref_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2775_, v_toPure_2776_, v_sep_2777_, v_ref_2778_);
lean_dec(v_ref_2778_);
lean_dec_ref(v_elems_2775_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_sep_2782_, lean_object* v_elems_2783_){
_start:
{
lean_object* v_toApplicative_2784_; lean_object* v_toBind_2785_; lean_object* v_getRef_2786_; lean_object* v_toPure_2787_; lean_object* v___f_2788_; lean_object* v___x_2789_; 
v_toApplicative_2784_ = lean_ctor_get(v_inst_2780_, 0);
lean_inc_ref(v_toApplicative_2784_);
v_toBind_2785_ = lean_ctor_get(v_inst_2780_, 1);
lean_inc(v_toBind_2785_);
lean_dec_ref(v_inst_2780_);
v_getRef_2786_ = lean_ctor_get(v_inst_2781_, 0);
lean_inc(v_getRef_2786_);
lean_dec_ref(v_inst_2781_);
v_toPure_2787_ = lean_ctor_get(v_toApplicative_2784_, 1);
lean_inc(v_toPure_2787_);
lean_dec_ref(v_toApplicative_2784_);
v___f_2788_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2788_, 0, v_elems_2783_);
lean_closure_set(v___f_2788_, 1, v_toPure_2787_);
lean_closure_set(v___f_2788_, 2, v_sep_2782_);
v___x_2789_ = lean_apply_4(v_toBind_2785_, lean_box(0), lean_box(0), v_getRef_2786_, v___f_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_sep_2793_, lean_object* v_elems_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2791_, v_inst_2792_, v_sep_2793_, v_elems_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2796_, lean_object* v_elems_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2796_, v_elems_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2799_, lean_object* v_elems_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2799_, v_elems_2800_);
lean_dec_ref(v_elems_2800_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2802_, lean_object* v_sep_2803_, lean_object* v_elems_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2803_, v_elems_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2806_, lean_object* v_sep_2807_, lean_object* v_elems_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2806_, v_sep_2807_, v_elems_2808_);
lean_dec_ref(v_elems_2808_);
lean_dec(v_k_2806_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2810_, lean_object* v_sep_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2812_, 0, v_k_2810_);
lean_closure_set(v___x_2812_, 1, v_sep_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2819_, lean_object* v_x_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2821_ = lean_array_get_size(v_x_2820_);
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = lean_nat_dec_eq(v___x_2821_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2824_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2825_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2826_ = lean_box(2);
v___x_2827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
lean_ctor_set(v___x_2827_, 1, v___x_2825_);
lean_ctor_set(v___x_2827_, 2, v_x_2820_);
v___x_2828_ = lean_unsigned_to_nat(2u);
v___x_2829_ = lean_mk_empty_array_with_capacity(v___x_2828_);
v___x_2830_ = lean_array_push(v___x_2829_, v_fn_2819_);
v___x_2831_ = lean_array_push(v___x_2830_, v___x_2827_);
v___x_2832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2826_);
lean_ctor_set(v___x_2832_, 1, v___x_2824_);
lean_ctor_set(v___x_2832_, 2, v___x_2831_);
return v___x_2832_;
}
else
{
lean_dec_ref(v_x_2820_);
return v_fn_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2833_, lean_object* v_args_2834_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = l_Lean_mkCIdent(v_fn_2833_);
v___x_2836_ = l_Lean_Syntax_mkApp(v___x_2835_, v_args_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2837_, lean_object* v_val_2838_, lean_object* v_info_2839_){
_start:
{
lean_object* v_atom_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_atom_2840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2840_, 0, v_info_2839_);
lean_ctor_set(v_atom_2840_, 1, v_val_2838_);
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_mk_empty_array_with_capacity(v___x_2841_);
v___x_2843_ = lean_array_push(v___x_2842_, v_atom_2840_);
v___x_2844_ = lean_box(2);
v___x_2845_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v_kind_2837_);
lean_ctor_set(v___x_2845_, 2, v___x_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2849_, lean_object* v_info_2850_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2852_ = l_Char_quote(v_val_2849_);
v___x_2853_ = l_Lean_Syntax_mkLit(v___x_2851_, v___x_2852_, v_info_2850_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2854_, lean_object* v_info_2855_){
_start:
{
uint32_t v_val_boxed_2856_; lean_object* v_res_2857_; 
v_val_boxed_2856_ = lean_unbox_uint32(v_val_2854_);
lean_dec(v_val_2854_);
v_res_2857_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2856_, v_info_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2861_, lean_object* v_info_2862_){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2864_ = l_String_quote(v_val_2861_);
v___x_2865_ = l_Lean_Syntax_mkLit(v___x_2863_, v___x_2864_, v_info_2862_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2869_, lean_object* v_info_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2872_ = l_Lean_Syntax_mkLit(v___x_2871_, v_val_2869_, v_info_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2873_, lean_object* v_info_2874_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2876_ = l_Nat_reprFast(v_val_2873_);
v___x_2877_ = l_Lean_Syntax_mkLit(v___x_2875_, v___x_2876_, v_info_2874_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2881_, lean_object* v_info_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2884_ = l_Lean_Syntax_mkLit(v___x_2883_, v_val_2881_, v_info_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2888_, lean_object* v_info_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2891_ = l_Lean_Syntax_mkLit(v___x_2890_, v_val_2888_, v_info_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2892_, lean_object* v_i_2893_, lean_object* v_val_2894_){
_start:
{
uint8_t v___x_2895_; 
v___x_2895_ = lean_string_utf8_at_end(v_s_2892_, v_i_2893_);
if (v___x_2895_ == 0)
{
uint32_t v_c_2896_; uint32_t v___x_2897_; uint8_t v___x_2898_; 
v_c_2896_ = lean_string_utf8_get(v_s_2892_, v_i_2893_);
v___x_2897_ = 48;
v___x_2898_ = lean_uint32_dec_eq(v_c_2896_, v___x_2897_);
if (v___x_2898_ == 0)
{
uint32_t v___x_2899_; uint8_t v___x_2900_; 
v___x_2899_ = 49;
v___x_2900_ = lean_uint32_dec_eq(v_c_2896_, v___x_2899_);
if (v___x_2900_ == 0)
{
uint32_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 95;
v___x_2902_ = lean_uint32_dec_eq(v_c_2896_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
lean_dec(v_val_2894_);
lean_dec(v_i_2893_);
v___x_2903_ = lean_box(0);
return v___x_2903_;
}
else
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_string_utf8_next(v_s_2892_, v_i_2893_);
lean_dec(v_i_2893_);
v_i_2893_ = v___x_2904_;
goto _start;
}
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2906_ = lean_string_utf8_next(v_s_2892_, v_i_2893_);
lean_dec(v_i_2893_);
v___x_2907_ = lean_unsigned_to_nat(2u);
v___x_2908_ = lean_nat_mul(v___x_2907_, v_val_2894_);
lean_dec(v_val_2894_);
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = lean_nat_add(v___x_2908_, v___x_2909_);
lean_dec(v___x_2908_);
v_i_2893_ = v___x_2906_;
v_val_2894_ = v___x_2910_;
goto _start;
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_string_utf8_next(v_s_2892_, v_i_2893_);
lean_dec(v_i_2893_);
v___x_2913_ = lean_unsigned_to_nat(2u);
v___x_2914_ = lean_nat_mul(v___x_2913_, v_val_2894_);
lean_dec(v_val_2894_);
v_i_2893_ = v___x_2912_;
v_val_2894_ = v___x_2914_;
goto _start;
}
}
else
{
lean_object* v___x_2916_; 
lean_dec(v_i_2893_);
v___x_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_val_2894_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2917_, lean_object* v_i_2918_, lean_object* v_val_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2917_, v_i_2918_, v_val_2919_);
lean_dec_ref(v_s_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2921_, lean_object* v_i_2922_, lean_object* v_val_2923_){
_start:
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_string_utf8_at_end(v_s_2921_, v_i_2922_);
if (v___x_2924_ == 0)
{
uint32_t v_c_2925_; uint8_t v___y_2927_; uint32_t v___x_2941_; uint8_t v___x_2942_; 
v_c_2925_ = lean_string_utf8_get(v_s_2921_, v_i_2922_);
v___x_2941_ = 48;
v___x_2942_ = lean_uint32_dec_le(v___x_2941_, v_c_2925_);
if (v___x_2942_ == 0)
{
v___y_2927_ = v___x_2924_;
goto v___jp_2926_;
}
else
{
uint32_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = 55;
v___x_2944_ = lean_uint32_dec_le(v_c_2925_, v___x_2943_);
v___y_2927_ = v___x_2944_;
goto v___jp_2926_;
}
v___jp_2926_:
{
if (v___y_2927_ == 0)
{
uint32_t v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = 95;
v___x_2929_ = lean_uint32_dec_eq(v_c_2925_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
lean_dec(v_val_2923_);
lean_dec(v_i_2922_);
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_string_utf8_next(v_s_2921_, v_i_2922_);
lean_dec(v_i_2922_);
v_i_2922_ = v___x_2931_;
goto _start;
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2933_ = lean_string_utf8_next(v_s_2921_, v_i_2922_);
lean_dec(v_i_2922_);
v___x_2934_ = lean_unsigned_to_nat(8u);
v___x_2935_ = lean_nat_mul(v___x_2934_, v_val_2923_);
lean_dec(v_val_2923_);
v___x_2936_ = lean_uint32_to_nat(v_c_2925_);
v___x_2937_ = lean_nat_add(v___x_2935_, v___x_2936_);
lean_dec(v___x_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_unsigned_to_nat(48u);
v___x_2939_ = lean_nat_sub(v___x_2937_, v___x_2938_);
lean_dec(v___x_2937_);
v_i_2922_ = v___x_2933_;
v_val_2923_ = v___x_2939_;
goto _start;
}
}
}
else
{
lean_object* v___x_2945_; 
lean_dec(v_i_2922_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_val_2923_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2946_, lean_object* v_i_2947_, lean_object* v_val_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2946_, v_i_2947_, v_val_2948_);
lean_dec_ref(v_s_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2950_, lean_object* v_i_2951_){
_start:
{
uint32_t v_c_2952_; lean_object* v_i_2953_; uint32_t v___x_2980_; uint8_t v___x_2981_; 
v_c_2952_ = lean_string_utf8_get(v_s_2950_, v_i_2951_);
v_i_2953_ = lean_string_utf8_next(v_s_2950_, v_i_2951_);
v___x_2980_ = 48;
v___x_2981_ = lean_uint32_dec_le(v___x_2980_, v_c_2952_);
if (v___x_2981_ == 0)
{
goto v___jp_2968_;
}
else
{
uint32_t v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = 57;
v___x_2983_ = lean_uint32_dec_le(v_c_2952_, v___x_2982_);
if (v___x_2983_ == 0)
{
goto v___jp_2968_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2984_ = lean_uint32_to_nat(v_c_2952_);
v___x_2985_ = lean_unsigned_to_nat(48u);
v___x_2986_ = lean_nat_sub(v___x_2984_, v___x_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v_i_2953_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
}
v___jp_2954_:
{
uint32_t v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = 65;
v___x_2956_ = lean_uint32_dec_le(v___x_2955_, v_c_2952_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_dec(v_i_2953_);
v___x_2957_ = lean_box(0);
return v___x_2957_;
}
else
{
uint32_t v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = 70;
v___x_2959_ = lean_uint32_dec_le(v_c_2952_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
lean_dec(v_i_2953_);
v___x_2960_ = lean_box(0);
return v___x_2960_;
}
else
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2961_ = lean_unsigned_to_nat(10u);
v___x_2962_ = lean_uint32_to_nat(v_c_2952_);
v___x_2963_ = lean_nat_add(v___x_2961_, v___x_2962_);
lean_dec(v___x_2962_);
v___x_2964_ = lean_unsigned_to_nat(65u);
v___x_2965_ = lean_nat_sub(v___x_2963_, v___x_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_i_2953_);
v___x_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
return v___x_2967_;
}
}
}
v___jp_2968_:
{
uint32_t v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = 97;
v___x_2970_ = lean_uint32_dec_le(v___x_2969_, v_c_2952_);
if (v___x_2970_ == 0)
{
goto v___jp_2954_;
}
else
{
uint32_t v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = 102;
v___x_2972_ = lean_uint32_dec_le(v_c_2952_, v___x_2971_);
if (v___x_2972_ == 0)
{
goto v___jp_2954_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2973_ = lean_unsigned_to_nat(10u);
v___x_2974_ = lean_uint32_to_nat(v_c_2952_);
v___x_2975_ = lean_nat_add(v___x_2973_, v___x_2974_);
lean_dec(v___x_2974_);
v___x_2976_ = lean_unsigned_to_nat(97u);
v___x_2977_ = lean_nat_sub(v___x_2975_, v___x_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v_i_2953_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2989_, lean_object* v_i_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2989_, v_i_2990_);
lean_dec(v_i_2990_);
lean_dec_ref(v_s_2989_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2992_, lean_object* v_i_2993_, lean_object* v_val_2994_){
_start:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_string_utf8_at_end(v_s_2992_, v_i_2993_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2992_, v_i_2993_);
if (lean_obj_tag(v___x_2996_) == 0)
{
uint32_t v___x_2997_; uint32_t v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_string_utf8_get(v_s_2992_, v_i_2993_);
v___x_2998_ = 95;
v___x_2999_ = lean_uint32_dec_eq(v___x_2997_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v_val_2994_);
lean_dec(v_i_2993_);
v___x_3000_ = lean_box(0);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_string_utf8_next(v_s_2992_, v_i_2993_);
lean_dec(v_i_2993_);
v_i_2993_ = v___x_3001_;
goto _start;
}
}
else
{
lean_object* v_val_3003_; lean_object* v_fst_3004_; lean_object* v_snd_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v_i_2993_);
v_val_3003_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_val_3003_);
lean_dec_ref_known(v___x_2996_, 1);
v_fst_3004_ = lean_ctor_get(v_val_3003_, 0);
lean_inc(v_fst_3004_);
v_snd_3005_ = lean_ctor_get(v_val_3003_, 1);
lean_inc(v_snd_3005_);
lean_dec(v_val_3003_);
v___x_3006_ = lean_unsigned_to_nat(16u);
v___x_3007_ = lean_nat_mul(v___x_3006_, v_val_2994_);
lean_dec(v_val_2994_);
v___x_3008_ = lean_nat_add(v___x_3007_, v_fst_3004_);
lean_dec(v_fst_3004_);
lean_dec(v___x_3007_);
v_i_2993_ = v_snd_3005_;
v_val_2994_ = v___x_3008_;
goto _start;
}
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_i_2993_);
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_val_2994_);
return v___x_3010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3011_, lean_object* v_i_3012_, lean_object* v_val_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3011_, v_i_3012_, v_val_3013_);
lean_dec_ref(v_s_3011_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3015_, lean_object* v_i_3016_, lean_object* v_val_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_string_utf8_at_end(v_s_3015_, v_i_3016_);
if (v___x_3018_ == 0)
{
uint32_t v_c_3019_; uint8_t v___y_3021_; uint32_t v___x_3035_; uint8_t v___x_3036_; 
v_c_3019_ = lean_string_utf8_get(v_s_3015_, v_i_3016_);
v___x_3035_ = 48;
v___x_3036_ = lean_uint32_dec_le(v___x_3035_, v_c_3019_);
if (v___x_3036_ == 0)
{
v___y_3021_ = v___x_3018_;
goto v___jp_3020_;
}
else
{
uint32_t v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = 57;
v___x_3038_ = lean_uint32_dec_le(v_c_3019_, v___x_3037_);
v___y_3021_ = v___x_3038_;
goto v___jp_3020_;
}
v___jp_3020_:
{
if (v___y_3021_ == 0)
{
uint32_t v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = 95;
v___x_3023_ = lean_uint32_dec_eq(v_c_3019_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_dec(v_val_3017_);
lean_dec(v_i_3016_);
v___x_3024_ = lean_box(0);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_string_utf8_next(v_s_3015_, v_i_3016_);
lean_dec(v_i_3016_);
v_i_3016_ = v___x_3025_;
goto _start;
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3027_ = lean_string_utf8_next(v_s_3015_, v_i_3016_);
lean_dec(v_i_3016_);
v___x_3028_ = lean_unsigned_to_nat(10u);
v___x_3029_ = lean_nat_mul(v___x_3028_, v_val_3017_);
lean_dec(v_val_3017_);
v___x_3030_ = lean_uint32_to_nat(v_c_3019_);
v___x_3031_ = lean_nat_add(v___x_3029_, v___x_3030_);
lean_dec(v___x_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_unsigned_to_nat(48u);
v___x_3033_ = lean_nat_sub(v___x_3031_, v___x_3032_);
lean_dec(v___x_3031_);
v_i_3016_ = v___x_3027_;
v_val_3017_ = v___x_3033_;
goto _start;
}
}
}
else
{
lean_object* v___x_3039_; 
lean_dec(v_i_3016_);
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_val_3017_);
return v___x_3039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3040_, lean_object* v_i_3041_, lean_object* v_val_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3040_, v_i_3041_, v_val_3042_);
lean_dec_ref(v_s_3040_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3046_){
_start:
{
lean_object* v_len_3047_; lean_object* v___x_3048_; uint8_t v___x_3058_; 
v_len_3047_ = lean_string_length(v_s_3046_);
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_nat_dec_eq(v_len_3047_, v___x_3048_);
if (v___x_3058_ == 0)
{
uint32_t v_c_3059_; uint32_t v___x_3060_; uint8_t v___x_3061_; 
v_c_3059_ = lean_string_utf8_get(v_s_3046_, v___x_3048_);
v___x_3060_ = 48;
v___x_3061_ = lean_uint32_dec_eq(v_c_3059_, v___x_3060_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
lean_dec(v_len_3047_);
v___x_3062_ = lean_uint32_dec_le(v___x_3060_, v_c_3059_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
else
{
uint32_t v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = 57;
v___x_3065_ = lean_uint32_dec_le(v_c_3059_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_box(0);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3046_, v___x_3048_, v___x_3048_);
return v___x_3067_;
}
}
}
else
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = lean_unsigned_to_nat(1u);
v___x_3069_ = lean_nat_dec_eq(v_len_3047_, v___x_3068_);
lean_dec(v_len_3047_);
if (v___x_3069_ == 0)
{
uint32_t v_c_3070_; uint32_t v___x_3071_; uint8_t v___x_3072_; 
v_c_3070_ = lean_string_utf8_get(v_s_3046_, v___x_3068_);
v___x_3071_ = 120;
v___x_3072_ = lean_uint32_dec_eq(v_c_3070_, v___x_3071_);
if (v___x_3072_ == 0)
{
uint32_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = 88;
v___x_3074_ = lean_uint32_dec_eq(v_c_3070_, v___x_3073_);
if (v___x_3074_ == 0)
{
uint32_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = 98;
v___x_3076_ = lean_uint32_dec_eq(v_c_3070_, v___x_3075_);
if (v___x_3076_ == 0)
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 66;
v___x_3078_ = lean_uint32_dec_eq(v_c_3070_, v___x_3077_);
if (v___x_3078_ == 0)
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 111;
v___x_3080_ = lean_uint32_dec_eq(v_c_3070_, v___x_3079_);
if (v___x_3080_ == 0)
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 79;
v___x_3082_ = lean_uint32_dec_eq(v_c_3070_, v___x_3081_);
if (v___x_3082_ == 0)
{
uint8_t v___x_3083_; 
v___x_3083_ = lean_uint32_dec_le(v___x_3060_, v_c_3070_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_box(0);
return v___x_3084_;
}
else
{
uint32_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = 57;
v___x_3086_ = lean_uint32_dec_le(v_c_3070_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_box(0);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3046_, v___x_3048_, v___x_3048_);
return v___x_3088_;
}
}
}
else
{
goto v___jp_3049_;
}
}
else
{
goto v___jp_3049_;
}
}
else
{
goto v___jp_3052_;
}
}
else
{
goto v___jp_3052_;
}
}
else
{
goto v___jp_3055_;
}
}
else
{
goto v___jp_3055_;
}
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3089_;
}
}
}
else
{
lean_object* v___x_3090_; 
lean_dec(v_len_3047_);
v___x_3090_ = lean_box(0);
return v___x_3090_;
}
v___jp_3049_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3046_, v___x_3050_, v___x_3048_);
return v___x_3051_;
}
v___jp_3052_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_unsigned_to_nat(2u);
v___x_3054_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3046_, v___x_3053_, v___x_3048_);
return v___x_3054_;
}
v___jp_3055_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(2u);
v___x_3057_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3046_, v___x_3056_, v___x_3048_);
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3091_);
lean_dec_ref(v_s_3091_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3093_, lean_object* v_stx_3094_){
_start:
{
if (lean_obj_tag(v_stx_3094_) == 1)
{
lean_object* v_kind_3095_; lean_object* v_args_3096_; uint8_t v___y_3098_; uint8_t v___x_3105_; 
v_kind_3095_ = lean_ctor_get(v_stx_3094_, 1);
v_args_3096_ = lean_ctor_get(v_stx_3094_, 2);
v___x_3105_ = lean_name_eq(v_kind_3095_, v_litKind_3093_);
if (v___x_3105_ == 0)
{
v___y_3098_ = v___x_3105_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_array_get_size(v_args_3096_);
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = lean_nat_dec_eq(v___x_3106_, v___x_3107_);
v___y_3098_ = v___x_3108_;
goto v___jp_3097_;
}
v___jp_3097_:
{
if (v___y_3098_ == 0)
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = lean_array_fget_borrowed(v_args_3096_, v___x_3100_);
if (lean_obj_tag(v___x_3101_) == 2)
{
lean_object* v_val_3102_; lean_object* v___x_3103_; 
v_val_3102_ = lean_ctor_get(v___x_3101_, 1);
lean_inc_ref(v_val_3102_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_val_3102_);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_box(0);
return v___x_3104_;
}
}
}
}
else
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_box(0);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3110_, lean_object* v_stx_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Syntax_isLit_x3f(v_litKind_3110_, v_stx_3111_);
lean_dec(v_stx_3111_);
lean_dec(v_litKind_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3113_, lean_object* v_stx_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Syntax_isLit_x3f(v_litKind_3113_, v_stx_3114_);
if (lean_obj_tag(v___x_3115_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3117_; 
v_val_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v___x_3115_, 1);
v___x_3117_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3116_);
lean_dec(v_val_3116_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; 
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3119_, lean_object* v_stx_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3119_, v_stx_3120_);
lean_dec(v_stx_3120_);
lean_dec(v_litKind_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3122_){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3124_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3123_, v_s_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Syntax_isNatLit_x3f(v_s_3125_);
lean_dec(v_s_3125_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3130_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3132_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3131_, v_s_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3133_);
lean_dec(v_s_3133_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3135_, lean_object* v_i_3136_, lean_object* v_val_3137_, lean_object* v_e_3138_, uint8_t v_sign_3139_, lean_object* v_exp_3140_){
_start:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_string_utf8_at_end(v_s_3135_, v_i_3136_);
if (v___x_3141_ == 0)
{
uint32_t v_c_3142_; uint8_t v___y_3144_; uint32_t v___x_3158_; uint8_t v___x_3159_; 
v_c_3142_ = lean_string_utf8_get(v_s_3135_, v_i_3136_);
v___x_3158_ = 48;
v___x_3159_ = lean_uint32_dec_le(v___x_3158_, v_c_3142_);
if (v___x_3159_ == 0)
{
v___y_3144_ = v___x_3141_;
goto v___jp_3143_;
}
else
{
uint32_t v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = 57;
v___x_3161_ = lean_uint32_dec_le(v_c_3142_, v___x_3160_);
v___y_3144_ = v___x_3161_;
goto v___jp_3143_;
}
v___jp_3143_:
{
if (v___y_3144_ == 0)
{
uint32_t v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = 95;
v___x_3146_ = lean_uint32_dec_eq(v_c_3142_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v_exp_3140_);
lean_dec(v_val_3137_);
lean_dec(v_i_3136_);
v___x_3147_ = lean_box(0);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_string_utf8_next(v_s_3135_, v_i_3136_);
lean_dec(v_i_3136_);
v_i_3136_ = v___x_3148_;
goto _start;
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3150_ = lean_string_utf8_next(v_s_3135_, v_i_3136_);
lean_dec(v_i_3136_);
v___x_3151_ = lean_unsigned_to_nat(10u);
v___x_3152_ = lean_nat_mul(v___x_3151_, v_exp_3140_);
lean_dec(v_exp_3140_);
v___x_3153_ = lean_uint32_to_nat(v_c_3142_);
v___x_3154_ = lean_nat_add(v___x_3152_, v___x_3153_);
lean_dec(v___x_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_unsigned_to_nat(48u);
v___x_3156_ = lean_nat_sub(v___x_3154_, v___x_3155_);
lean_dec(v___x_3154_);
v_i_3136_ = v___x_3150_;
v_exp_3140_ = v___x_3156_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3136_);
if (v_sign_3139_ == 0)
{
uint8_t v___x_3162_; 
v___x_3162_ = lean_nat_dec_le(v_e_3138_, v_exp_3140_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3163_ = lean_nat_sub(v_e_3138_, v_exp_3140_);
lean_dec(v_exp_3140_);
v___x_3164_ = lean_box(v___x_3141_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___x_3163_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v_val_3137_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3168_ = lean_nat_sub(v_exp_3140_, v_e_3138_);
lean_dec(v_exp_3140_);
v___x_3169_ = lean_box(v_sign_3139_);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v_val_3137_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3173_ = lean_nat_add(v_exp_3140_, v_e_3138_);
lean_dec(v_exp_3140_);
v___x_3174_ = lean_box(v_sign_3139_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set(v___x_3175_, 1, v___x_3173_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_val_3137_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3178_, lean_object* v_i_3179_, lean_object* v_val_3180_, lean_object* v_e_3181_, lean_object* v_sign_3182_, lean_object* v_exp_3183_){
_start:
{
uint8_t v_sign_boxed_3184_; lean_object* v_res_3185_; 
v_sign_boxed_3184_ = lean_unbox(v_sign_3182_);
v_res_3185_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3178_, v_i_3179_, v_val_3180_, v_e_3181_, v_sign_boxed_3184_, v_exp_3183_);
lean_dec(v_e_3181_);
lean_dec_ref(v_s_3178_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3186_, lean_object* v_i_3187_, lean_object* v_val_3188_, lean_object* v_e_3189_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_string_utf8_at_end(v_s_3186_, v_i_3187_);
if (v___x_3190_ == 0)
{
uint32_t v_c_3191_; uint32_t v___x_3192_; uint8_t v___x_3193_; 
v_c_3191_ = lean_string_utf8_get(v_s_3186_, v_i_3187_);
v___x_3192_ = 45;
v___x_3193_ = lean_uint32_dec_eq(v_c_3191_, v___x_3192_);
if (v___x_3193_ == 0)
{
uint32_t v___x_3194_; uint8_t v___x_3195_; 
v___x_3194_ = 43;
v___x_3195_ = lean_uint32_dec_eq(v_c_3191_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3186_, v_i_3187_, v_val_3188_, v_e_3189_, v___x_3195_, v___x_3196_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_string_utf8_next(v_s_3186_, v_i_3187_);
lean_dec(v_i_3187_);
v___x_3199_ = lean_unsigned_to_nat(0u);
v___x_3200_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3186_, v___x_3198_, v_val_3188_, v_e_3189_, v___x_3193_, v___x_3199_);
return v___x_3200_;
}
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_string_utf8_next(v_s_3186_, v_i_3187_);
lean_dec(v_i_3187_);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3186_, v___x_3201_, v_val_3188_, v_e_3189_, v___x_3193_, v___x_3202_);
return v___x_3203_;
}
}
else
{
lean_object* v___x_3204_; 
lean_dec(v_val_3188_);
lean_dec(v_i_3187_);
v___x_3204_ = lean_box(0);
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3205_, lean_object* v_i_3206_, lean_object* v_val_3207_, lean_object* v_e_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3205_, v_i_3206_, v_val_3207_, v_e_3208_);
lean_dec(v_e_3208_);
lean_dec_ref(v_s_3205_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3210_, lean_object* v_i_3211_, lean_object* v_val_3212_, lean_object* v_e_3213_){
_start:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_string_utf8_at_end(v_s_3210_, v_i_3211_);
if (v___x_3217_ == 0)
{
uint32_t v_c_3218_; uint8_t v___y_3220_; uint32_t v___x_3240_; uint8_t v___x_3241_; 
v_c_3218_ = lean_string_utf8_get(v_s_3210_, v_i_3211_);
v___x_3240_ = 48;
v___x_3241_ = lean_uint32_dec_le(v___x_3240_, v_c_3218_);
if (v___x_3241_ == 0)
{
v___y_3220_ = v___x_3217_;
goto v___jp_3219_;
}
else
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 57;
v___x_3243_ = lean_uint32_dec_le(v_c_3218_, v___x_3242_);
v___y_3220_ = v___x_3243_;
goto v___jp_3219_;
}
v___jp_3219_:
{
if (v___y_3220_ == 0)
{
uint32_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = 95;
v___x_3222_ = lean_uint32_dec_eq(v_c_3218_, v___x_3221_);
if (v___x_3222_ == 0)
{
uint32_t v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = 101;
v___x_3224_ = lean_uint32_dec_eq(v_c_3218_, v___x_3223_);
if (v___x_3224_ == 0)
{
uint32_t v___x_3225_; uint8_t v___x_3226_; 
v___x_3225_ = 69;
v___x_3226_ = lean_uint32_dec_eq(v_c_3218_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; 
lean_dec(v_e_3213_);
lean_dec(v_val_3212_);
lean_dec(v_i_3211_);
v___x_3227_ = lean_box(0);
return v___x_3227_;
}
else
{
goto v___jp_3214_;
}
}
else
{
goto v___jp_3214_;
}
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_string_utf8_next(v_s_3210_, v_i_3211_);
lean_dec(v_i_3211_);
v_i_3211_ = v___x_3228_;
goto _start;
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3230_ = lean_string_utf8_next(v_s_3210_, v_i_3211_);
lean_dec(v_i_3211_);
v___x_3231_ = lean_unsigned_to_nat(10u);
v___x_3232_ = lean_nat_mul(v___x_3231_, v_val_3212_);
lean_dec(v_val_3212_);
v___x_3233_ = lean_uint32_to_nat(v_c_3218_);
v___x_3234_ = lean_nat_add(v___x_3232_, v___x_3233_);
lean_dec(v___x_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_unsigned_to_nat(48u);
v___x_3236_ = lean_nat_sub(v___x_3234_, v___x_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_add(v_e_3213_, v___x_3237_);
lean_dec(v_e_3213_);
v_i_3211_ = v___x_3230_;
v_val_3212_ = v___x_3236_;
v_e_3213_ = v___x_3238_;
goto _start;
}
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec(v_i_3211_);
v___x_3244_ = lean_box(v___x_3217_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v_e_3213_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_val_3212_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
v___jp_3214_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_string_utf8_next(v_s_3210_, v_i_3211_);
lean_dec(v_i_3211_);
v___x_3216_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3210_, v___x_3215_, v_val_3212_, v_e_3213_);
lean_dec(v_e_3213_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3248_, lean_object* v_i_3249_, lean_object* v_val_3250_, lean_object* v_e_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3248_, v_i_3249_, v_val_3250_, v_e_3251_);
lean_dec_ref(v_s_3248_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3253_, lean_object* v_i_3254_, lean_object* v_val_3255_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_string_utf8_at_end(v_s_3253_, v_i_3254_);
if (v___x_3260_ == 0)
{
uint32_t v_c_3261_; uint8_t v___y_3263_; uint32_t v___x_3286_; uint8_t v___x_3287_; 
v_c_3261_ = lean_string_utf8_get(v_s_3253_, v_i_3254_);
v___x_3286_ = 48;
v___x_3287_ = lean_uint32_dec_le(v___x_3286_, v_c_3261_);
if (v___x_3287_ == 0)
{
v___y_3263_ = v___x_3260_;
goto v___jp_3262_;
}
else
{
uint32_t v___x_3288_; uint8_t v___x_3289_; 
v___x_3288_ = 57;
v___x_3289_ = lean_uint32_dec_le(v_c_3261_, v___x_3288_);
v___y_3263_ = v___x_3289_;
goto v___jp_3262_;
}
v___jp_3262_:
{
if (v___y_3263_ == 0)
{
uint32_t v___x_3264_; uint8_t v___x_3265_; 
v___x_3264_ = 95;
v___x_3265_ = lean_uint32_dec_eq(v_c_3261_, v___x_3264_);
if (v___x_3265_ == 0)
{
uint32_t v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = 46;
v___x_3267_ = lean_uint32_dec_eq(v_c_3261_, v___x_3266_);
if (v___x_3267_ == 0)
{
uint32_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = 101;
v___x_3269_ = lean_uint32_dec_eq(v_c_3261_, v___x_3268_);
if (v___x_3269_ == 0)
{
uint32_t v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = 69;
v___x_3271_ = lean_uint32_dec_eq(v_c_3261_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
lean_dec(v_val_3255_);
lean_dec(v_i_3254_);
v___x_3272_ = lean_box(0);
return v___x_3272_;
}
else
{
goto v___jp_3256_;
}
}
else
{
goto v___jp_3256_;
}
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_string_utf8_next(v_s_3253_, v_i_3254_);
lean_dec(v_i_3254_);
v___x_3274_ = lean_unsigned_to_nat(0u);
v___x_3275_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3253_, v___x_3273_, v_val_3255_, v___x_3274_);
return v___x_3275_;
}
}
else
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_string_utf8_next(v_s_3253_, v_i_3254_);
lean_dec(v_i_3254_);
v_i_3254_ = v___x_3276_;
goto _start;
}
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3278_ = lean_string_utf8_next(v_s_3253_, v_i_3254_);
lean_dec(v_i_3254_);
v___x_3279_ = lean_unsigned_to_nat(10u);
v___x_3280_ = lean_nat_mul(v___x_3279_, v_val_3255_);
lean_dec(v_val_3255_);
v___x_3281_ = lean_uint32_to_nat(v_c_3261_);
v___x_3282_ = lean_nat_add(v___x_3280_, v___x_3281_);
lean_dec(v___x_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_unsigned_to_nat(48u);
v___x_3284_ = lean_nat_sub(v___x_3282_, v___x_3283_);
lean_dec(v___x_3282_);
v_i_3254_ = v___x_3278_;
v_val_3255_ = v___x_3284_;
goto _start;
}
}
}
else
{
lean_object* v___x_3290_; 
lean_dec(v_val_3255_);
lean_dec(v_i_3254_);
v___x_3290_ = lean_box(0);
return v___x_3290_;
}
v___jp_3256_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_string_utf8_next(v_s_3253_, v_i_3254_);
lean_dec(v_i_3254_);
v___x_3258_ = lean_unsigned_to_nat(0u);
v___x_3259_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3253_, v___x_3257_, v_val_3255_, v___x_3258_);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3291_, lean_object* v_i_3292_, lean_object* v_val_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3291_, v_i_3292_, v_val_3293_);
lean_dec_ref(v_s_3291_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3295_){
_start:
{
lean_object* v_len_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v_len_3296_ = lean_string_length(v_s_3295_);
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = lean_nat_dec_eq(v_len_3296_, v___x_3297_);
lean_dec(v_len_3296_);
if (v___x_3298_ == 0)
{
uint32_t v_c_3299_; uint32_t v___x_3300_; uint8_t v___x_3301_; 
v_c_3299_ = lean_string_utf8_get(v_s_3295_, v___x_3297_);
v___x_3300_ = 48;
v___x_3301_ = lean_uint32_dec_le(v___x_3300_, v_c_3299_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_box(0);
return v___x_3302_;
}
else
{
uint32_t v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = 57;
v___x_3304_ = lean_uint32_dec_le(v_c_3299_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_box(0);
return v___x_3305_;
}
else
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3295_, v___x_3297_, v___x_3297_);
return v___x_3306_;
}
}
}
else
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_box(0);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3308_);
lean_dec_ref(v_s_3308_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3312_ = l_Lean_Syntax_isLit_x3f(v___x_3311_, v_stx_3310_);
if (lean_obj_tag(v___x_3312_) == 1)
{
lean_object* v_val_3313_; lean_object* v___x_3314_; 
v_val_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_val_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3313_);
lean_dec(v_val_3313_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; 
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3316_);
lean_dec(v_stx_3316_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3318_){
_start:
{
switch(lean_obj_tag(v_x_3318_))
{
case 2:
{
lean_object* v_val_3319_; lean_object* v___x_3320_; 
v_val_3319_ = lean_ctor_get(v_x_3318_, 1);
lean_inc_ref(v_val_3319_);
lean_dec_ref_known(v_x_3318_, 2);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_val_3319_);
return v___x_3320_;
}
case 3:
{
lean_object* v_rawVal_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_rawVal_3321_ = lean_ctor_get(v_x_3318_, 1);
lean_inc_ref(v_rawVal_3321_);
lean_dec_ref_known(v_x_3318_, 4);
v___x_3322_ = lean_substring_tostring(v_rawVal_3321_);
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
default: 
{
lean_object* v___x_3324_; 
lean_dec(v_x_3318_);
v___x_3324_ = lean_box(0);
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_unsigned_to_nat(0u);
return v___x_3327_;
}
else
{
lean_object* v_val_3328_; 
v_val_3328_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___x_3326_, 1);
return v_val_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_Syntax_toNat(v_stx_3329_);
lean_dec(v_stx_3329_);
return v_res_3330_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = 9;
v___x_3332_ = lean_box_uint32(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = 10;
v___x_3334_ = lean_box_uint32(v___x_3333_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = 13;
v___x_3336_ = lean_box_uint32(v___x_3335_);
return v___x_3336_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = 39;
v___x_3338_ = lean_box_uint32(v___x_3337_);
return v___x_3338_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = 34;
v___x_3340_ = lean_box_uint32(v___x_3339_);
return v___x_3340_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = 92;
v___x_3342_ = lean_box_uint32(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3343_, lean_object* v_i_3344_){
_start:
{
uint32_t v_c_3345_; lean_object* v_i_3346_; uint32_t v___x_3347_; uint8_t v___x_3348_; 
v_c_3345_ = lean_string_utf8_get(v_s_3343_, v_i_3344_);
v_i_3346_ = lean_string_utf8_next(v_s_3343_, v_i_3344_);
v___x_3347_ = 92;
v___x_3348_ = lean_uint32_dec_eq(v_c_3345_, v___x_3347_);
if (v___x_3348_ == 0)
{
uint32_t v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = 34;
v___x_3350_ = lean_uint32_dec_eq(v_c_3345_, v___x_3349_);
if (v___x_3350_ == 0)
{
uint32_t v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = 39;
v___x_3352_ = lean_uint32_dec_eq(v_c_3345_, v___x_3351_);
if (v___x_3352_ == 0)
{
uint32_t v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = 114;
v___x_3354_ = lean_uint32_dec_eq(v_c_3345_, v___x_3353_);
if (v___x_3354_ == 0)
{
uint32_t v___x_3355_; uint8_t v___x_3356_; 
v___x_3355_ = 110;
v___x_3356_ = lean_uint32_dec_eq(v_c_3345_, v___x_3355_);
if (v___x_3356_ == 0)
{
uint32_t v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = 116;
v___x_3358_ = lean_uint32_dec_eq(v_c_3345_, v___x_3357_);
if (v___x_3358_ == 0)
{
uint32_t v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = 120;
v___x_3360_ = lean_uint32_dec_eq(v_c_3345_, v___x_3359_);
if (v___x_3360_ == 0)
{
uint32_t v___x_3361_; uint8_t v___x_3362_; 
v___x_3361_ = 117;
v___x_3362_ = lean_uint32_dec_eq(v_c_3345_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_dec(v_i_3346_);
v___x_3363_ = lean_box(0);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3343_, v_i_3346_);
lean_dec(v_i_3346_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_box(0);
return v___x_3365_;
}
else
{
lean_object* v_val_3366_; lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v___x_3369_; 
v_val_3366_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_val_3366_);
lean_dec_ref_known(v___x_3364_, 1);
v_fst_3367_ = lean_ctor_get(v_val_3366_, 0);
lean_inc(v_fst_3367_);
v_snd_3368_ = lean_ctor_get(v_val_3366_, 1);
lean_inc(v_snd_3368_);
lean_dec(v_val_3366_);
v___x_3369_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3343_, v_snd_3368_);
lean_dec(v_snd_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3370_; 
lean_dec(v_fst_3367_);
v___x_3370_ = lean_box(0);
return v___x_3370_;
}
else
{
lean_object* v_val_3371_; lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3374_; 
v_val_3371_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v___x_3369_, 1);
v_fst_3372_ = lean_ctor_get(v_val_3371_, 0);
lean_inc(v_fst_3372_);
v_snd_3373_ = lean_ctor_get(v_val_3371_, 1);
lean_inc(v_snd_3373_);
lean_dec(v_val_3371_);
v___x_3374_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3343_, v_snd_3373_);
lean_dec(v_snd_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; 
lean_dec(v_fst_3372_);
lean_dec(v_fst_3367_);
v___x_3375_ = lean_box(0);
return v___x_3375_;
}
else
{
lean_object* v_val_3376_; lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3379_; 
v_val_3376_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v___x_3374_, 1);
v_fst_3377_ = lean_ctor_get(v_val_3376_, 0);
lean_inc(v_fst_3377_);
v_snd_3378_ = lean_ctor_get(v_val_3376_, 1);
lean_inc(v_snd_3378_);
lean_dec(v_val_3376_);
v___x_3379_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3343_, v_snd_3378_);
lean_dec(v_snd_3378_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v___x_3380_; 
lean_dec(v_fst_3377_);
lean_dec(v_fst_3372_);
lean_dec(v_fst_3367_);
v___x_3380_ = lean_box(0);
return v___x_3380_;
}
else
{
lean_object* v_val_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3406_; 
v_val_3381_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3383_ = v___x_3379_;
v_isShared_3384_ = v_isSharedCheck_3406_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_val_3381_);
lean_dec(v___x_3379_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3406_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_fst_3385_; lean_object* v_snd_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3405_; 
v_fst_3385_ = lean_ctor_get(v_val_3381_, 0);
v_snd_3386_ = lean_ctor_get(v_val_3381_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_val_3381_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3388_ = v_val_3381_;
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_snd_3386_);
lean_inc(v_fst_3385_);
lean_dec(v_val_3381_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint32_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3390_ = lean_unsigned_to_nat(16u);
v___x_3391_ = lean_nat_mul(v___x_3390_, v_fst_3367_);
lean_dec(v_fst_3367_);
v___x_3392_ = lean_nat_add(v___x_3391_, v_fst_3372_);
lean_dec(v_fst_3372_);
lean_dec(v___x_3391_);
v___x_3393_ = lean_nat_mul(v___x_3390_, v___x_3392_);
lean_dec(v___x_3392_);
v___x_3394_ = lean_nat_add(v___x_3393_, v_fst_3377_);
lean_dec(v_fst_3377_);
lean_dec(v___x_3393_);
v___x_3395_ = lean_nat_mul(v___x_3390_, v___x_3394_);
lean_dec(v___x_3394_);
v___x_3396_ = lean_nat_add(v___x_3395_, v_fst_3385_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3395_);
v___x_3397_ = l_Char_ofNat(v___x_3396_);
lean_dec(v___x_3396_);
v___x_3398_ = lean_box_uint32(v___x_3397_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3398_);
v___x_3400_ = v___x_3388_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_snd_3386_);
v___x_3400_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3402_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3400_);
v___x_3402_ = v___x_3383_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
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
lean_object* v___x_3407_; 
v___x_3407_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3343_, v_i_3346_);
lean_dec(v_i_3346_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_box(0);
return v___x_3408_;
}
else
{
lean_object* v_val_3409_; lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3412_; 
v_val_3409_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_val_3409_);
lean_dec_ref_known(v___x_3407_, 1);
v_fst_3410_ = lean_ctor_get(v_val_3409_, 0);
lean_inc(v_fst_3410_);
v_snd_3411_ = lean_ctor_get(v_val_3409_, 1);
lean_inc(v_snd_3411_);
lean_dec(v_val_3409_);
v___x_3412_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3343_, v_snd_3411_);
lean_dec(v_snd_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v___x_3413_; 
lean_dec(v_fst_3410_);
v___x_3413_ = lean_box(0);
return v___x_3413_;
}
else
{
lean_object* v_val_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3435_; 
v_val_3414_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3416_ = v___x_3412_;
v_isShared_3417_ = v_isSharedCheck_3435_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_val_3414_);
lean_dec(v___x_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3435_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_fst_3418_; lean_object* v_snd_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3434_; 
v_fst_3418_ = lean_ctor_get(v_val_3414_, 0);
v_snd_3419_ = lean_ctor_get(v_val_3414_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_val_3414_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3421_ = v_val_3414_;
v_isShared_3422_ = v_isSharedCheck_3434_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3419_);
lean_inc(v_fst_3418_);
lean_dec(v_val_3414_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3434_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint32_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3423_ = lean_unsigned_to_nat(16u);
v___x_3424_ = lean_nat_mul(v___x_3423_, v_fst_3410_);
lean_dec(v_fst_3410_);
v___x_3425_ = lean_nat_add(v___x_3424_, v_fst_3418_);
lean_dec(v_fst_3418_);
lean_dec(v___x_3424_);
v___x_3426_ = l_Char_ofNat(v___x_3425_);
lean_dec(v___x_3425_);
v___x_3427_ = lean_box_uint32(v___x_3426_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3427_);
v___x_3429_ = v___x_3421_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_snd_3419_);
v___x_3429_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3429_);
v___x_3431_ = v___x_3416_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
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
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v_i_3346_);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v_i_3346_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v_i_3346_);
v___x_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v_i_3346_);
v___x_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
return v___x_3447_;
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
lean_ctor_set(v___x_3449_, 1, v_i_3346_);
v___x_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v_i_3346_);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3454_, lean_object* v_i_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Syntax_decodeQuotedChar(v_s_3454_, v_i_3455_);
lean_dec(v_i_3455_);
lean_dec_ref(v_s_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3457_){
_start:
{
uint32_t v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = 32;
v___x_3459_ = lean_uint32_dec_eq(v___y_3457_, v___x_3458_);
if (v___x_3459_ == 0)
{
uint32_t v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = 9;
v___x_3461_ = lean_uint32_dec_eq(v___y_3457_, v___x_3460_);
if (v___x_3461_ == 0)
{
uint32_t v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = 13;
v___x_3463_ = lean_uint32_dec_eq(v___y_3457_, v___x_3462_);
if (v___x_3463_ == 0)
{
uint32_t v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = 10;
v___x_3465_ = lean_uint32_dec_eq(v___y_3457_, v___x_3464_);
return v___x_3465_;
}
else
{
return v___x_3463_;
}
}
else
{
return v___x_3461_;
}
}
else
{
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3466_){
_start:
{
uint32_t v___y_264__boxed_3467_; uint8_t v_res_3468_; lean_object* v_r_3469_; 
v___y_264__boxed_3467_ = lean_unbox_uint32(v___y_3466_);
lean_dec(v___y_3466_);
v_res_3468_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_264__boxed_3467_);
v_r_3469_ = lean_box(v_res_3468_);
return v_r_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3471_, lean_object* v_i_3472_){
_start:
{
lean_object* v___f_3473_; uint32_t v___x_3478_; uint32_t v___x_3479_; uint8_t v___x_3480_; 
v___f_3473_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3478_ = lean_string_utf8_get(v_s_3471_, v_i_3472_);
v___x_3479_ = 32;
v___x_3480_ = lean_uint32_dec_eq(v___x_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
uint32_t v___x_3481_; uint8_t v___x_3482_; 
v___x_3481_ = 9;
v___x_3482_ = lean_uint32_dec_eq(v___x_3478_, v___x_3481_);
if (v___x_3482_ == 0)
{
uint32_t v___x_3483_; uint8_t v___x_3484_; 
v___x_3483_ = 13;
v___x_3484_ = lean_uint32_dec_eq(v___x_3478_, v___x_3483_);
if (v___x_3484_ == 0)
{
uint32_t v___x_3485_; uint8_t v___x_3486_; 
v___x_3485_ = 10;
v___x_3486_ = lean_uint32_dec_eq(v___x_3478_, v___x_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref(v_s_3471_);
v___x_3487_ = lean_box(0);
return v___x_3487_;
}
else
{
goto v___jp_3474_;
}
}
else
{
goto v___jp_3474_;
}
}
else
{
goto v___jp_3474_;
}
}
else
{
goto v___jp_3474_;
}
v___jp_3474_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = lean_string_utf8_next(v_s_3471_, v_i_3472_);
v___x_3476_ = lean_string_nextwhile(v_s_3471_, v___f_3473_, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3488_, lean_object* v_i_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Syntax_decodeStringGap(v_s_3488_, v_i_3489_);
lean_dec(v_i_3489_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3491_, lean_object* v_i_3492_, lean_object* v_acc_3493_){
_start:
{
uint32_t v_c_3494_; uint32_t v___x_3495_; uint8_t v___x_3496_; 
v_c_3494_ = lean_string_utf8_get(v_s_3491_, v_i_3492_);
v___x_3495_ = 34;
v___x_3496_ = lean_uint32_dec_eq(v_c_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v_i_3497_; uint8_t v___x_3498_; 
v_i_3497_ = lean_string_utf8_next(v_s_3491_, v_i_3492_);
lean_dec(v_i_3492_);
v___x_3498_ = lean_string_utf8_at_end(v_s_3491_, v_i_3497_);
if (v___x_3498_ == 0)
{
uint32_t v___x_3499_; uint8_t v___x_3500_; 
v___x_3499_ = 92;
v___x_3500_ = lean_uint32_dec_eq(v_c_3494_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_string_push(v_acc_3493_, v_c_3494_);
v_i_3492_ = v_i_3497_;
v_acc_3493_ = v___x_3501_;
goto _start;
}
else
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Syntax_decodeQuotedChar(v_s_3491_, v_i_3497_);
if (lean_obj_tag(v___x_3503_) == 1)
{
lean_object* v_val_3504_; lean_object* v_fst_3505_; lean_object* v_snd_3506_; uint32_t v___x_3507_; lean_object* v___x_3508_; 
lean_dec(v_i_3497_);
v_val_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v_fst_3505_ = lean_ctor_get(v_val_3504_, 0);
lean_inc(v_fst_3505_);
v_snd_3506_ = lean_ctor_get(v_val_3504_, 1);
lean_inc(v_snd_3506_);
lean_dec(v_val_3504_);
v___x_3507_ = lean_unbox_uint32(v_fst_3505_);
lean_dec(v_fst_3505_);
v___x_3508_ = lean_string_push(v_acc_3493_, v___x_3507_);
v_i_3492_ = v_snd_3506_;
v_acc_3493_ = v___x_3508_;
goto _start;
}
else
{
lean_object* v___x_3510_; 
lean_dec(v___x_3503_);
lean_inc_ref(v_s_3491_);
v___x_3510_ = l_Lean_Syntax_decodeStringGap(v_s_3491_, v_i_3497_);
lean_dec(v_i_3497_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; 
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v_i_3492_ = v_val_3511_;
goto _start;
}
else
{
lean_object* v___x_3513_; 
lean_dec(v___x_3510_);
lean_dec_ref(v_acc_3493_);
lean_dec_ref(v_s_3491_);
v___x_3513_ = lean_box(0);
return v___x_3513_;
}
}
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v_i_3497_);
lean_dec_ref(v_acc_3493_);
lean_dec_ref(v_s_3491_);
v___x_3514_ = lean_box(0);
return v___x_3514_;
}
}
else
{
lean_object* v___x_3515_; 
lean_dec(v_i_3492_);
lean_dec_ref(v_s_3491_);
v___x_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3515_, 0, v_acc_3493_);
return v___x_3515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3516_, lean_object* v_i_3517_, lean_object* v_num_3518_){
_start:
{
uint32_t v_c_3519_; lean_object* v_i_3520_; uint32_t v___x_3521_; uint8_t v___x_3522_; 
v_c_3519_ = lean_string_utf8_get(v_s_3516_, v_i_3517_);
v_i_3520_ = lean_string_utf8_next(v_s_3516_, v_i_3517_);
lean_dec(v_i_3517_);
v___x_3521_ = 35;
v___x_3522_ = lean_uint32_dec_eq(v_c_3519_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3523_ = lean_string_utf8_byte_size(v_s_3516_);
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_add(v_num_3518_, v___x_3524_);
lean_dec(v_num_3518_);
v___x_3526_ = lean_nat_sub(v___x_3523_, v___x_3525_);
lean_dec(v___x_3525_);
v___x_3527_ = lean_string_utf8_extract(v_s_3516_, v_i_3520_, v___x_3526_);
lean_dec(v___x_3526_);
lean_dec(v_i_3520_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_unsigned_to_nat(1u);
v___x_3529_ = lean_nat_add(v_num_3518_, v___x_3528_);
lean_dec(v_num_3518_);
v_i_3517_ = v_i_3520_;
v_num_3518_ = v___x_3529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3531_, lean_object* v_i_3532_, lean_object* v_num_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3531_, v_i_3532_, v_num_3533_);
lean_dec_ref(v_s_3531_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3535_){
_start:
{
lean_object* v___x_3536_; uint32_t v___x_3537_; uint32_t v___x_3538_; uint8_t v___x_3539_; 
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_string_utf8_get(v_s_3535_, v___x_3536_);
v___x_3538_ = 114;
v___x_3539_ = lean_uint32_dec_eq(v___x_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = lean_unsigned_to_nat(1u);
v___x_3541_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3542_ = l_Lean_Syntax_decodeStrLitAux(v_s_3535_, v___x_3540_, v___x_3541_);
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = lean_unsigned_to_nat(1u);
v___x_3544_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3535_, v___x_3543_, v___x_3536_);
lean_dec_ref(v_s_3535_);
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3546_){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3548_ = l_Lean_Syntax_isLit_x3f(v___x_3547_, v_stx_3546_);
if (lean_obj_tag(v___x_3548_) == 1)
{
lean_object* v_val_3549_; lean_object* v___x_3550_; 
v_val_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_val_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = l_Lean_Syntax_decodeStrLit(v_val_3549_);
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; 
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
return v___x_3551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3552_);
lean_dec(v_stx_3552_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3554_){
_start:
{
lean_object* v___x_3555_; uint32_t v_c_3556_; uint32_t v___x_3557_; uint8_t v___x_3558_; 
v___x_3555_ = lean_unsigned_to_nat(1u);
v_c_3556_ = lean_string_utf8_get(v_s_3554_, v___x_3555_);
v___x_3557_ = 92;
v___x_3558_ = lean_uint32_dec_eq(v_c_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_box_uint32(v_c_3556_);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = lean_unsigned_to_nat(2u);
v___x_3562_ = l_Lean_Syntax_decodeQuotedChar(v_s_3554_, v___x_3561_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_box(0);
return v___x_3563_;
}
else
{
lean_object* v_val_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3572_; 
v_val_3564_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3566_ = v___x_3562_;
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_val_3564_);
lean_dec(v___x_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v_fst_3568_; lean_object* v___x_3570_; 
v_fst_3568_ = lean_ctor_get(v_val_3564_, 0);
lean_inc(v_fst_3568_);
lean_dec(v_val_3564_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v_fst_3568_);
v___x_3570_ = v___x_3566_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_fst_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Syntax_decodeCharLit(v_s_3573_);
lean_dec_ref(v_s_3573_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3575_){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3577_ = l_Lean_Syntax_isLit_x3f(v___x_3576_, v_stx_3575_);
if (lean_obj_tag(v___x_3577_) == 1)
{
lean_object* v_val_3578_; lean_object* v___x_3579_; 
v_val_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_val_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_Lean_Syntax_decodeCharLit(v_val_3578_);
lean_dec(v_val_3578_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; 
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
return v___x_3580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3581_);
lean_dec(v_stx_3581_);
return v_res_3582_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3583_){
_start:
{
uint8_t v___y_3601_; uint32_t v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = 65;
v___x_3607_ = lean_uint32_dec_le(v___x_3606_, v___y_3583_);
if (v___x_3607_ == 0)
{
v___y_3601_ = v___x_3607_;
goto v___jp_3600_;
}
else
{
uint32_t v___x_3608_; uint8_t v___x_3609_; 
v___x_3608_ = 90;
v___x_3609_ = lean_uint32_dec_le(v___y_3583_, v___x_3608_);
v___y_3601_ = v___x_3609_;
goto v___jp_3600_;
}
v___jp_3584_:
{
uint32_t v___x_3585_; uint8_t v___x_3586_; 
v___x_3585_ = 95;
v___x_3586_ = lean_uint32_dec_eq(v___y_3583_, v___x_3585_);
if (v___x_3586_ == 0)
{
uint32_t v___x_3587_; uint8_t v___x_3588_; 
v___x_3587_ = 39;
v___x_3588_ = lean_uint32_dec_eq(v___y_3583_, v___x_3587_);
if (v___x_3588_ == 0)
{
uint32_t v___x_3589_; uint8_t v___x_3590_; 
v___x_3589_ = 33;
v___x_3590_ = lean_uint32_dec_eq(v___y_3583_, v___x_3589_);
if (v___x_3590_ == 0)
{
uint32_t v___x_3591_; uint8_t v___x_3592_; 
v___x_3591_ = 63;
v___x_3592_ = lean_uint32_dec_eq(v___y_3583_, v___x_3591_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = l_Lean_isLetterLike(v___y_3583_);
if (v___x_3593_ == 0)
{
uint8_t v___x_3594_; 
v___x_3594_ = l_Lean_isSubScriptAlnum(v___y_3583_);
return v___x_3594_;
}
else
{
return v___x_3593_;
}
}
else
{
return v___x_3592_;
}
}
else
{
return v___x_3590_;
}
}
else
{
return v___x_3588_;
}
}
else
{
return v___x_3586_;
}
}
v___jp_3595_:
{
uint32_t v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = 48;
v___x_3597_ = lean_uint32_dec_le(v___x_3596_, v___y_3583_);
if (v___x_3597_ == 0)
{
goto v___jp_3584_;
}
else
{
uint32_t v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = 57;
v___x_3599_ = lean_uint32_dec_le(v___y_3583_, v___x_3598_);
if (v___x_3599_ == 0)
{
goto v___jp_3584_;
}
else
{
return v___x_3599_;
}
}
}
v___jp_3600_:
{
if (v___y_3601_ == 0)
{
uint32_t v___x_3602_; uint8_t v___x_3603_; 
v___x_3602_ = 97;
v___x_3603_ = lean_uint32_dec_le(v___x_3602_, v___y_3583_);
if (v___x_3603_ == 0)
{
goto v___jp_3595_;
}
else
{
uint32_t v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = 122;
v___x_3605_ = lean_uint32_dec_le(v___y_3583_, v___x_3604_);
if (v___x_3605_ == 0)
{
goto v___jp_3595_;
}
else
{
return v___x_3605_;
}
}
}
else
{
return v___y_3601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3610_){
_start:
{
uint32_t v___y_509__boxed_3611_; uint8_t v_res_3612_; lean_object* v_r_3613_; 
v___y_509__boxed_3611_ = lean_unbox_uint32(v___y_3610_);
lean_dec(v___y_3610_);
v_res_3612_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_509__boxed_3611_);
v_r_3613_ = lean_box(v_res_3612_);
return v_r_3613_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3614_, uint32_t v___x_3615_, uint32_t v___y_3616_){
_start:
{
uint8_t v___x_3617_; 
v___x_3617_ = lean_uint32_dec_le(v___x_3614_, v___y_3616_);
if (v___x_3617_ == 0)
{
return v___x_3617_;
}
else
{
uint8_t v___x_3618_; 
v___x_3618_ = lean_uint32_dec_le(v___y_3616_, v___x_3615_);
return v___x_3618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3619_, lean_object* v___x_3620_, lean_object* v___y_3621_){
_start:
{
uint32_t v___x_564__boxed_3622_; uint32_t v___x_565__boxed_3623_; uint32_t v___y_566__boxed_3624_; uint8_t v_res_3625_; lean_object* v_r_3626_; 
v___x_564__boxed_3622_ = lean_unbox_uint32(v___x_3619_);
lean_dec(v___x_3619_);
v___x_565__boxed_3623_ = lean_unbox_uint32(v___x_3620_);
lean_dec(v___x_3620_);
v___y_566__boxed_3624_ = lean_unbox_uint32(v___y_3621_);
lean_dec(v___y_3621_);
v_res_3625_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_564__boxed_3622_, v___x_565__boxed_3623_, v___y_566__boxed_3624_);
v_r_3626_ = lean_box(v_res_3625_);
return v_r_3626_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3627_, uint8_t v___x_3628_, uint32_t v_x_3629_){
_start:
{
uint32_t v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = 187;
v___x_3631_ = lean_uint32_dec_eq(v_x_3629_, v___x_3630_);
if (v___x_3631_ == 0)
{
return v___x_3627_;
}
else
{
return v___x_3628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3632_, lean_object* v___x_3633_, lean_object* v_x_3634_){
_start:
{
uint8_t v___x_577__boxed_3635_; uint8_t v___x_578__boxed_3636_; uint32_t v_x_579__boxed_3637_; uint8_t v_res_3638_; lean_object* v_r_3639_; 
v___x_577__boxed_3635_ = lean_unbox(v___x_3632_);
v___x_578__boxed_3636_ = lean_unbox(v___x_3633_);
v_x_579__boxed_3637_ = lean_unbox_uint32(v_x_3634_);
lean_dec(v_x_3634_);
v_res_3638_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_577__boxed_3635_, v___x_578__boxed_3636_, v_x_579__boxed_3637_);
v_r_3639_ = lean_box(v_res_3638_);
return v_r_3639_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = 48;
v___x_3642_ = lean_box_uint32(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = 57;
v___x_3644_ = lean_box_uint32(v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___f_3647_; 
v___x_3645_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3646_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3647_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3647_, 0, v___x_3645_);
lean_closure_set(v___f_3647_, 1, v___x_3646_);
return v___f_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3648_, lean_object* v_acc_3649_){
_start:
{
lean_object* v_ss_3651_; lean_object* v_acc_3652_; uint8_t v___x_3661_; 
lean_inc_ref(v_ss_3648_);
v___x_3661_ = lean_substring_isempty(v_ss_3648_);
if (v___x_3661_ == 0)
{
uint32_t v_curr_3662_; uint32_t v___x_3663_; uint8_t v___x_3664_; 
lean_inc_ref(v_ss_3648_);
v_curr_3662_ = lean_substring_front(v_ss_3648_);
v___x_3663_ = 171;
v___x_3664_ = lean_uint32_dec_eq(v_curr_3662_, v___x_3663_);
if (v___x_3664_ == 0)
{
lean_object* v___f_3665_; uint8_t v___y_3697_; uint32_t v___x_3702_; uint8_t v___x_3703_; 
v___f_3665_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3702_ = 65;
v___x_3703_ = lean_uint32_dec_le(v___x_3702_, v_curr_3662_);
if (v___x_3703_ == 0)
{
v___y_3697_ = v___x_3703_;
goto v___jp_3696_;
}
else
{
uint32_t v___x_3704_; uint8_t v___x_3705_; 
v___x_3704_ = 90;
v___x_3705_ = lean_uint32_dec_le(v_curr_3662_, v___x_3704_);
v___y_3697_ = v___x_3705_;
goto v___jp_3696_;
}
v___jp_3666_:
{
lean_object* v_idPart_3667_; lean_object* v_startPos_3668_; lean_object* v_stopPos_3669_; lean_object* v_startPos_3670_; lean_object* v_stopPos_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_inc_ref(v_ss_3648_);
v_idPart_3667_ = lean_substring_takewhile(v_ss_3648_, v___f_3665_);
v_startPos_3668_ = lean_ctor_get(v_idPart_3667_, 1);
lean_inc(v_startPos_3668_);
v_stopPos_3669_ = lean_ctor_get(v_idPart_3667_, 2);
lean_inc(v_stopPos_3669_);
v_startPos_3670_ = lean_ctor_get(v_ss_3648_, 1);
v_stopPos_3671_ = lean_ctor_get(v_ss_3648_, 2);
v___x_3672_ = lean_nat_sub(v_stopPos_3669_, v_startPos_3668_);
lean_dec(v_startPos_3668_);
lean_dec(v_stopPos_3669_);
v___x_3673_ = lean_nat_sub(v_stopPos_3671_, v_startPos_3670_);
v___x_3674_ = lean_substring_extract(v_ss_3648_, v___x_3672_, v___x_3673_);
v___x_3675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3675_, 0, v_idPart_3667_);
lean_ctor_set(v___x_3675_, 1, v_acc_3649_);
v_ss_3651_ = v___x_3674_;
v_acc_3652_ = v___x_3675_;
goto v___jp_3650_;
}
v___jp_3676_:
{
uint32_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3677_ = 95;
v___x_3678_ = lean_uint32_dec_eq(v_curr_3662_, v___x_3677_);
if (v___x_3678_ == 0)
{
uint8_t v___x_3679_; 
v___x_3679_ = l_Lean_isLetterLike(v_curr_3662_);
if (v___x_3679_ == 0)
{
uint32_t v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = 48;
v___x_3681_ = lean_uint32_dec_le(v___x_3680_, v_curr_3662_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_dec(v_acc_3649_);
lean_dec_ref(v_ss_3648_);
v___x_3682_ = lean_box(0);
return v___x_3682_;
}
else
{
uint32_t v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = 57;
v___x_3684_ = lean_uint32_dec_le(v_curr_3662_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; 
lean_dec(v_acc_3649_);
lean_dec_ref(v_ss_3648_);
v___x_3685_ = lean_box(0);
return v___x_3685_;
}
else
{
lean_object* v___f_3686_; lean_object* v_idPart_3687_; lean_object* v_startPos_3688_; lean_object* v_stopPos_3689_; lean_object* v_startPos_3690_; lean_object* v_stopPos_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___f_3686_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3648_);
v_idPart_3687_ = lean_substring_takewhile(v_ss_3648_, v___f_3686_);
v_startPos_3688_ = lean_ctor_get(v_idPart_3687_, 1);
lean_inc(v_startPos_3688_);
v_stopPos_3689_ = lean_ctor_get(v_idPart_3687_, 2);
lean_inc(v_stopPos_3689_);
v_startPos_3690_ = lean_ctor_get(v_ss_3648_, 1);
v_stopPos_3691_ = lean_ctor_get(v_ss_3648_, 2);
v___x_3692_ = lean_nat_sub(v_stopPos_3689_, v_startPos_3688_);
lean_dec(v_startPos_3688_);
lean_dec(v_stopPos_3689_);
v___x_3693_ = lean_nat_sub(v_stopPos_3691_, v_startPos_3690_);
v___x_3694_ = lean_substring_extract(v_ss_3648_, v___x_3692_, v___x_3693_);
v___x_3695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3695_, 0, v_idPart_3687_);
lean_ctor_set(v___x_3695_, 1, v_acc_3649_);
v_ss_3651_ = v___x_3694_;
v_acc_3652_ = v___x_3695_;
goto v___jp_3650_;
}
}
}
else
{
goto v___jp_3666_;
}
}
else
{
goto v___jp_3666_;
}
}
v___jp_3696_:
{
if (v___y_3697_ == 0)
{
uint32_t v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = 97;
v___x_3699_ = lean_uint32_dec_le(v___x_3698_, v_curr_3662_);
if (v___x_3699_ == 0)
{
goto v___jp_3676_;
}
else
{
uint32_t v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = 122;
v___x_3701_ = lean_uint32_dec_le(v_curr_3662_, v___x_3700_);
if (v___x_3701_ == 0)
{
goto v___jp_3676_;
}
else
{
goto v___jp_3666_;
}
}
}
else
{
goto v___jp_3666_;
}
}
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___f_3708_; lean_object* v_escapedPart_3709_; lean_object* v_str_3710_; lean_object* v_startPos_3711_; lean_object* v_stopPos_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3733_; 
v___x_3706_ = lean_box(v___x_3664_);
v___x_3707_ = lean_box(v___x_3661_);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3708_, 0, v___x_3706_);
lean_closure_set(v___f_3708_, 1, v___x_3707_);
lean_inc_ref(v_ss_3648_);
v_escapedPart_3709_ = lean_substring_takewhile(v_ss_3648_, v___f_3708_);
v_str_3710_ = lean_ctor_get(v_escapedPart_3709_, 0);
v_startPos_3711_ = lean_ctor_get(v_escapedPart_3709_, 1);
v_stopPos_3712_ = lean_ctor_get(v_escapedPart_3709_, 2);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_escapedPart_3709_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3714_ = v_escapedPart_3709_;
v_isShared_3715_ = v_isSharedCheck_3733_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_stopPos_3712_);
lean_inc(v_startPos_3711_);
lean_inc(v_str_3710_);
lean_dec(v_escapedPart_3709_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3733_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v_startPos_3716_; lean_object* v_stopPos_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_escapedPart_3721_; 
v_startPos_3716_ = lean_ctor_get(v_ss_3648_, 1);
v_stopPos_3717_ = lean_ctor_get(v_ss_3648_, 2);
v___x_3718_ = lean_string_utf8_next(v_str_3710_, v_stopPos_3712_);
lean_dec(v_stopPos_3712_);
lean_inc(v_stopPos_3717_);
v___x_3719_ = lean_string_pos_min(v_stopPos_3717_, v___x_3718_);
lean_inc(v___x_3719_);
lean_inc(v_startPos_3711_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 2, v___x_3719_);
v_escapedPart_3721_ = v___x_3714_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_str_3710_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_startPos_3711_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v___x_3719_);
v_escapedPart_3721_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; uint32_t v___x_3724_; uint32_t v___x_3725_; uint8_t v___x_3726_; 
v___x_3722_ = lean_nat_sub(v___x_3719_, v_startPos_3711_);
lean_dec(v_startPos_3711_);
lean_dec(v___x_3719_);
lean_inc(v___x_3722_);
lean_inc_ref_n(v_escapedPart_3721_, 2);
v___x_3723_ = lean_substring_prev(v_escapedPart_3721_, v___x_3722_);
v___x_3724_ = lean_substring_get(v_escapedPart_3721_, v___x_3723_);
v___x_3725_ = 187;
v___x_3726_ = lean_uint32_dec_eq(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; 
lean_dec(v___x_3722_);
lean_dec_ref(v_escapedPart_3721_);
lean_dec(v_acc_3649_);
lean_dec_ref(v_ss_3648_);
v___x_3727_ = lean_box(0);
return v___x_3727_;
}
else
{
if (v___x_3661_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = lean_nat_sub(v_stopPos_3717_, v_startPos_3716_);
v___x_3729_ = lean_substring_extract(v_ss_3648_, v___x_3722_, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_escapedPart_3721_);
lean_ctor_set(v___x_3730_, 1, v_acc_3649_);
v_ss_3651_ = v___x_3729_;
v_acc_3652_ = v___x_3730_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3731_; 
lean_dec(v___x_3722_);
lean_dec_ref(v_escapedPart_3721_);
lean_dec(v_acc_3649_);
lean_dec_ref(v_ss_3648_);
v___x_3731_ = lean_box(0);
return v___x_3731_;
}
}
}
}
}
}
else
{
lean_object* v___x_3734_; 
lean_dec(v_acc_3649_);
lean_dec_ref(v_ss_3648_);
v___x_3734_ = lean_box(0);
return v___x_3734_;
}
v___jp_3650_:
{
uint32_t v___x_3653_; uint32_t v___x_3654_; uint8_t v___x_3655_; 
lean_inc_ref(v_ss_3651_);
v___x_3653_ = lean_substring_front(v_ss_3651_);
v___x_3654_ = 46;
v___x_3655_ = lean_uint32_dec_eq(v___x_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_substring_isempty(v_ss_3651_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
lean_dec(v_acc_3652_);
v___x_3657_ = lean_box(0);
return v___x_3657_;
}
else
{
return v_acc_3652_;
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_substring_drop(v_ss_3651_, v___x_3658_);
v_ss_3648_ = v___x_3659_;
v_acc_3649_ = v_acc_3652_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3736_ = lean_box(0);
v___x_3737_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3735_, v___x_3736_);
v___x_3738_ = l_List_reverse___redArg(v___x_3737_);
return v___x_3738_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3742_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3743_ = lean_unsigned_to_nat(10u);
v___x_3744_ = lean_unsigned_to_nat(1253u);
v___x_3745_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3746_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3747_ = l_mkPanicMessageWithDecl(v___x_3746_, v___x_3745_, v___x_3744_, v___x_3743_, v___x_3742_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3748_, lean_object* v_x_3749_){
_start:
{
if (lean_obj_tag(v_x_3749_) == 0)
{
lean_inc(v_init_3748_);
return v_init_3748_;
}
else
{
lean_object* v_head_3750_; lean_object* v_tail_3751_; lean_object* v___x_3752_; lean_object* v_comp_3753_; uint32_t v___x_3754_; uint32_t v___x_3755_; uint8_t v___x_3756_; 
v_head_3750_ = lean_ctor_get(v_x_3749_, 0);
lean_inc(v_head_3750_);
v_tail_3751_ = lean_ctor_get(v_x_3749_, 1);
lean_inc(v_tail_3751_);
lean_dec_ref_known(v_x_3749_, 2);
v___x_3752_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3748_, v_tail_3751_);
v_comp_3753_ = lean_substring_tostring(v_head_3750_);
lean_inc_ref(v_comp_3753_);
v___x_3754_ = lean_string_front(v_comp_3753_);
v___x_3755_ = 171;
v___x_3756_ = lean_uint32_dec_eq(v___x_3754_, v___x_3755_);
if (v___x_3756_ == 0)
{
uint32_t v___x_3757_; uint8_t v___x_3758_; 
v___x_3757_ = 48;
v___x_3758_ = lean_uint32_dec_le(v___x_3757_, v___x_3754_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Name_str___override(v___x_3752_, v_comp_3753_);
return v___x_3759_;
}
else
{
uint32_t v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = 57;
v___x_3761_ = lean_uint32_dec_le(v___x_3754_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_Name_str___override(v___x_3752_, v_comp_3753_);
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3753_);
lean_dec_ref(v_comp_3753_);
if (lean_obj_tag(v___x_3763_) == 1)
{
lean_object* v_val_3764_; lean_object* v___x_3765_; 
v_val_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_val_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___x_3765_ = l_Lean_Name_num___override(v___x_3752_, v_val_3764_);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_dec(v___x_3763_);
lean_dec(v___x_3752_);
v___x_3766_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3767_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3766_);
return v___x_3767_;
}
}
}
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_string_drop(v_comp_3753_, v___x_3768_);
v___x_3770_ = lean_string_dropright(v___x_3769_, v___x_3768_);
v___x_3771_ = l_Lean_Name_str___override(v___x_3752_, v___x_3770_);
return v___x_3771_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3772_, lean_object* v_x_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3772_, v_x_3773_);
lean_dec(v_init_3772_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3775_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_box(0);
v___x_3777_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3775_, v___x_3776_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_box(0);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = lean_box(0);
v___x_3780_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3779_, v___x_3777_);
return v___x_3780_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3781_){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = lean_string_utf8_byte_size(v_s_3781_);
v___x_3784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3784_, 0, v_s_3781_);
lean_ctor_set(v___x_3784_, 1, v___x_3782_);
lean_ctor_set(v___x_3784_, 2, v___x_3783_);
v___x_3785_ = l_Substring_Raw_toName(v___x_3784_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3786_){
_start:
{
lean_object* v___x_3787_; uint32_t v___x_3788_; uint32_t v___x_3789_; uint8_t v___x_3790_; 
v___x_3787_ = lean_unsigned_to_nat(0u);
v___x_3788_ = lean_string_utf8_get(v_s_3786_, v___x_3787_);
v___x_3789_ = 96;
v___x_3790_ = lean_uint32_dec_eq(v___x_3788_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec_ref(v_s_3786_);
v___x_3791_ = lean_box(0);
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3792_ = lean_string_utf8_byte_size(v_s_3786_);
v___x_3793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3793_, 0, v_s_3786_);
lean_ctor_set(v___x_3793_, 1, v___x_3787_);
lean_ctor_set(v___x_3793_, 2, v___x_3792_);
v___x_3794_ = lean_unsigned_to_nat(1u);
v___x_3795_ = lean_substring_drop(v___x_3793_, v___x_3794_);
v___x_3796_ = l_Substring_Raw_toName(v___x_3795_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_box(0);
return v___x_3797_;
}
else
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
return v___x_3798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3799_){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3801_ = l_Lean_Syntax_isLit_x3f(v___x_3800_, v_stx_3799_);
if (lean_obj_tag(v___x_3801_) == 1)
{
lean_object* v_val_3802_; lean_object* v___x_3803_; 
v_val_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = l_Lean_Syntax_decodeNameLit(v_val_3802_);
return v___x_3803_;
}
else
{
lean_object* v___x_3804_; 
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3805_);
lean_dec(v_stx_3805_);
return v_res_3806_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3807_){
_start:
{
if (lean_obj_tag(v_x_3807_) == 1)
{
lean_object* v_args_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_args_3808_ = lean_ctor_get(v_x_3807_, 2);
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = lean_array_get_size(v_args_3808_);
v___x_3811_ = lean_nat_dec_lt(v___x_3809_, v___x_3810_);
return v___x_3811_;
}
else
{
uint8_t v___x_3812_; 
v___x_3812_ = 0;
return v___x_3812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3813_){
_start:
{
uint8_t v_res_3814_; lean_object* v_r_3815_; 
v_res_3814_ = l_Lean_Syntax_hasArgs(v_x_3813_);
lean_dec(v_x_3813_);
v_r_3815_ = lean_box(v_res_3814_);
return v_r_3815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3816_){
_start:
{
if (lean_obj_tag(v_x_3816_) == 2)
{
uint8_t v___x_3817_; 
v___x_3817_ = 1;
return v___x_3817_;
}
else
{
uint8_t v___x_3818_; 
v___x_3818_ = 0;
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3819_){
_start:
{
uint8_t v_res_3820_; lean_object* v_r_3821_; 
v_res_3820_ = l_Lean_Syntax_isAtom(v_x_3819_);
lean_dec(v_x_3819_);
v_r_3821_ = lean_box(v_res_3820_);
return v_r_3821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3822_, lean_object* v_x_3823_){
_start:
{
if (lean_obj_tag(v_x_3823_) == 2)
{
lean_object* v_val_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_val_3824_ = lean_ctor_get(v_x_3823_, 1);
lean_inc_ref(v_val_3824_);
lean_dec_ref_known(v_x_3823_, 2);
v___x_3825_ = lean_string_trim(v_val_3824_);
v___x_3826_ = lean_string_trim(v_token_3822_);
v___x_3827_ = lean_string_dec_eq(v___x_3825_, v___x_3826_);
lean_dec_ref(v___x_3826_);
lean_dec_ref(v___x_3825_);
return v___x_3827_;
}
else
{
uint8_t v___x_3828_; 
lean_dec(v_x_3823_);
lean_dec_ref(v_token_3822_);
v___x_3828_ = 0;
return v___x_3828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3829_, lean_object* v_x_3830_){
_start:
{
uint8_t v_res_3831_; lean_object* v_r_3832_; 
v_res_3831_ = l_Lean_Syntax_isToken(v_token_3829_, v_x_3830_);
v_r_3832_ = lean_box(v_res_3831_);
return v_r_3832_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3833_){
_start:
{
switch(lean_obj_tag(v_stx_3833_))
{
case 1:
{
lean_object* v_kind_3834_; lean_object* v_args_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v_kind_3834_ = lean_ctor_get(v_stx_3833_, 1);
v_args_3835_ = lean_ctor_get(v_stx_3833_, 2);
v___x_3836_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3837_ = lean_name_eq(v_kind_3834_, v___x_3836_);
if (v___x_3837_ == 0)
{
return v___x_3837_;
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3838_ = lean_array_get_size(v_args_3835_);
v___x_3839_ = lean_unsigned_to_nat(0u);
v___x_3840_ = lean_nat_dec_eq(v___x_3838_, v___x_3839_);
return v___x_3840_;
}
}
case 0:
{
uint8_t v___x_3841_; 
v___x_3841_ = 1;
return v___x_3841_;
}
default: 
{
uint8_t v___x_3842_; 
v___x_3842_ = 0;
return v___x_3842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3843_){
_start:
{
uint8_t v_res_3844_; lean_object* v_r_3845_; 
v_res_3844_ = l_Lean_Syntax_isNone(v_stx_3843_);
lean_dec(v_stx_3843_);
v_r_3845_ = lean_box(v_res_3844_);
return v_r_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_Syntax_getOptional_x3f(v_stx_3846_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_box(0);
return v___x_3848_;
}
else
{
lean_object* v_val_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3857_; 
v_val_3849_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3851_ = v___x_3847_;
v_isShared_3852_ = v_isSharedCheck_3857_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_val_3849_);
lean_dec(v___x_3847_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3857_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
v___x_3853_ = l_Lean_Syntax_getId(v_val_3849_);
lean_dec(v_val_3849_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v___x_3853_);
v___x_3855_ = v___x_3851_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3858_);
lean_dec(v_stx_3858_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3860_, lean_object* v_x_3861_){
_start:
{
if (lean_obj_tag(v_x_3861_) == 1)
{
lean_object* v_args_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_args_3862_ = lean_ctor_get(v_x_3861_, 2);
lean_inc_ref(v_p_3860_);
lean_inc_ref(v_x_3861_);
v___x_3863_ = lean_apply_1(v_p_3860_, v_x_3861_);
v___x_3864_ = lean_unbox(v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; size_t v_sz_3867_; size_t v___x_3868_; lean_object* v___x_3869_; lean_object* v_fst_3870_; 
lean_inc_ref(v_args_3862_);
lean_dec_ref_known(v_x_3861_, 3);
v___x_3865_ = lean_box(0);
v___x_3866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3867_ = lean_array_size(v_args_3862_);
v___x_3868_ = ((size_t)0ULL);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3860_, v_args_3862_, v_sz_3867_, v___x_3868_, v___x_3866_);
lean_dec_ref(v_args_3862_);
v_fst_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_fst_3870_);
lean_dec_ref(v___x_3869_);
if (lean_obj_tag(v_fst_3870_) == 0)
{
return v___x_3865_;
}
else
{
lean_object* v_val_3871_; 
v_val_3871_ = lean_ctor_get(v_fst_3870_, 0);
lean_inc(v_val_3871_);
lean_dec_ref_known(v_fst_3870_, 1);
return v_val_3871_;
}
}
else
{
lean_object* v___x_3872_; 
lean_dec_ref(v_p_3860_);
v___x_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_x_3861_);
return v___x_3872_;
}
}
else
{
lean_object* v___x_3873_; uint8_t v___x_3874_; 
lean_inc(v_x_3861_);
v___x_3873_ = lean_apply_1(v_p_3860_, v_x_3861_);
v___x_3874_ = lean_unbox(v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_dec(v_x_3861_);
v___x_3875_ = lean_box(0);
return v___x_3875_;
}
else
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_x_3861_);
return v___x_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3877_, lean_object* v_as_3878_, size_t v_sz_3879_, size_t v_i_3880_, lean_object* v_b_3881_){
_start:
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_usize_dec_lt(v_i_3880_, v_sz_3879_);
if (v___x_3882_ == 0)
{
lean_dec_ref(v_p_3877_);
lean_inc_ref(v_b_3881_);
return v_b_3881_;
}
else
{
lean_object* v___x_3883_; lean_object* v_a_3884_; lean_object* v___x_3885_; 
v___x_3883_ = lean_box(0);
v_a_3884_ = lean_array_uget_borrowed(v_as_3878_, v_i_3880_);
lean_inc(v_a_3884_);
lean_inc_ref(v_p_3877_);
v___x_3885_ = l_Lean_Syntax_findAux(v_p_3877_, v_a_3884_);
if (lean_obj_tag(v___x_3885_) == 1)
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
lean_dec_ref(v_p_3877_);
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___x_3883_);
return v___x_3887_;
}
else
{
lean_object* v___x_3888_; size_t v___x_3889_; size_t v___x_3890_; 
lean_dec(v___x_3885_);
v___x_3888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3889_ = ((size_t)1ULL);
v___x_3890_ = lean_usize_add(v_i_3880_, v___x_3889_);
v_i_3880_ = v___x_3890_;
v_b_3881_ = v___x_3888_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3892_, lean_object* v_as_3893_, lean_object* v_sz_3894_, lean_object* v_i_3895_, lean_object* v_b_3896_){
_start:
{
size_t v_sz_boxed_3897_; size_t v_i_boxed_3898_; lean_object* v_res_3899_; 
v_sz_boxed_3897_ = lean_unbox_usize(v_sz_3894_);
lean_dec(v_sz_3894_);
v_i_boxed_3898_ = lean_unbox_usize(v_i_3895_);
lean_dec(v_i_3895_);
v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3892_, v_as_3893_, v_sz_boxed_3897_, v_i_boxed_3898_, v_b_3896_);
lean_dec_ref(v_b_3896_);
lean_dec_ref(v_as_3893_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3900_, lean_object* v_p_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Syntax_findAux(v_p_3901_, v_stx_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3903_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_Syntax_isNatLit_x3f(v_s_3903_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_unsigned_to_nat(0u);
return v___x_3905_;
}
else
{
lean_object* v_val_3906_; 
v_val_3906_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_val_3906_);
lean_dec_ref_known(v___x_3904_, 1);
return v_val_3906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_TSyntax_getNat(v_s_3907_);
lean_dec(v_s_3907_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3912_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3914_ = l_Lean_Syntax_isLit_x3f(v___x_3913_, v_stx_3912_);
if (lean_obj_tag(v___x_3914_) == 1)
{
lean_object* v_val_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v_val_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_val_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = lean_unsigned_to_nat(0u);
v___x_3917_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3915_, v___x_3916_, v___x_3916_);
lean_dec(v_val_3915_);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; 
lean_dec(v___x_3914_);
v___x_3918_ = lean_box(0);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3919_);
lean_dec(v_stx_3919_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3921_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = lean_unsigned_to_nat(0u);
return v___x_3923_;
}
else
{
lean_object* v_val_3924_; 
v_val_3924_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_val_3924_);
lean_dec_ref_known(v___x_3922_, 1);
return v_val_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_TSyntax_getHexNumVal(v_s_3925_);
lean_dec(v_s_3925_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3927_, lean_object* v_p_3928_, lean_object* v_n_3929_){
_start:
{
uint8_t v___x_3930_; 
v___x_3930_ = lean_string_utf8_at_end(v_s_3927_, v_p_3928_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; uint32_t v___x_3932_; uint32_t v___x_3933_; uint8_t v___x_3934_; 
v___x_3931_ = lean_string_utf8_next(v_s_3927_, v_p_3928_);
v___x_3932_ = lean_string_utf8_get(v_s_3927_, v_p_3928_);
lean_dec(v_p_3928_);
v___x_3933_ = 95;
v___x_3934_ = lean_uint32_dec_eq(v___x_3932_, v___x_3933_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_unsigned_to_nat(1u);
v___x_3936_ = lean_nat_add(v_n_3929_, v___x_3935_);
lean_dec(v_n_3929_);
v_p_3928_ = v___x_3931_;
v_n_3929_ = v___x_3936_;
goto _start;
}
else
{
v_p_3928_ = v___x_3931_;
goto _start;
}
}
else
{
lean_dec(v_p_3928_);
return v_n_3929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3939_, lean_object* v_p_3940_, lean_object* v_n_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3939_, v_p_3940_, v_n_3941_);
lean_dec_ref(v_s_3939_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3943_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3945_ = l_Lean_Syntax_isLit_x3f(v___x_3944_, v_s_3943_);
if (lean_obj_tag(v___x_3945_) == 1)
{
lean_object* v_val_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_val_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_val_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3947_ = lean_unsigned_to_nat(0u);
v___x_3948_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3946_, v___x_3947_, v___x_3947_);
lean_dec(v_val_3946_);
return v___x_3948_;
}
else
{
lean_object* v___x_3949_; 
lean_dec(v___x_3945_);
v___x_3949_ = lean_unsigned_to_nat(0u);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_TSyntax_getHexNumSize(v_s_3950_);
lean_dec(v_s_3950_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3952_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Syntax_getId(v_s_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_TSyntax_getId(v_s_3954_);
lean_dec(v_s_3954_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3963_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v___x_3965_; 
v___x_3965_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3965_;
}
else
{
lean_object* v_val_3966_; 
v_val_3966_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_val_3966_);
lean_dec_ref_known(v___x_3964_, 1);
return v_val_3966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_TSyntax_getScientific(v_s_3967_);
lean_dec(v_s_3967_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Syntax_isStrLit_x3f(v_s_3969_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v___x_3971_; 
v___x_3971_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3971_;
}
else
{
lean_object* v_val_3972_; 
v_val_3972_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_val_3972_);
lean_dec_ref_known(v___x_3970_, 1);
return v_val_3972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Lean_TSyntax_getString(v_s_3973_);
lean_dec(v_s_3973_);
return v_res_3974_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Syntax_isCharLit_x3f(v_s_3975_);
if (lean_obj_tag(v___x_3976_) == 0)
{
uint32_t v___x_3977_; 
v___x_3977_ = 65;
return v___x_3977_;
}
else
{
lean_object* v_val_3978_; uint32_t v___x_3979_; 
v_val_3978_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3979_ = lean_unbox_uint32(v_val_3978_);
lean_dec(v_val_3978_);
return v___x_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3980_){
_start:
{
uint32_t v_res_3981_; lean_object* v_r_3982_; 
v_res_3981_ = l_Lean_TSyntax_getChar(v_s_3980_);
lean_dec(v_s_3980_);
v_r_3982_ = lean_box_uint32(v_res_3981_);
return v_r_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Syntax_isNameLit_x3f(v_s_3983_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_box(0);
return v___x_3985_;
}
else
{
lean_object* v_val_3986_; 
v_val_3986_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_val_3986_);
lean_dec_ref_known(v___x_3984_, 1);
return v_val_3986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_TSyntax_getName(v_s_3987_);
lean_dec(v_s_3987_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3989_){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = l_Lean_Syntax_getArg(v_s_3989_, v___x_3990_);
v___x_3992_ = l_Lean_Syntax_getId(v___x_3991_);
lean_dec(v___x_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_TSyntax_getHygieneInfo(v_s_3993_);
lean_dec(v_s_3993_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3995_, v_a_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3998_, v_a_3999_);
lean_dec_ref(v_a_3999_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_4001_){
_start:
{
lean_object* v___f_4002_; 
v___f_4002_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4002_, 0, v_sep_4001_);
return v___f_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_4003_, lean_object* v_sep_4004_){
_start:
{
lean_object* v___f_4005_; 
v___f_4005_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4005_, 0, v_sep_4004_);
return v___f_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_4006_, lean_object* v_sep_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_4006_, v_sep_4007_);
lean_dec(v_k_4006_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_4009_, lean_object* v_val_4010_, uint8_t v_canonical_4011_){
_start:
{
lean_object* v___x_4012_; lean_object* v_src_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v_imported_4016_; lean_object* v_ctx_4017_; lean_object* v_scopes_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4034_; 
v___x_4012_ = lean_unsigned_to_nat(0u);
v_src_4013_ = l_Lean_Syntax_getArg(v_s_4009_, v___x_4012_);
v___x_4014_ = l_Lean_Syntax_getId(v_src_4013_);
v___x_4015_ = l_Lean_extractMacroScopes(v___x_4014_);
v_imported_4016_ = lean_ctor_get(v___x_4015_, 1);
v_ctx_4017_ = lean_ctor_get(v___x_4015_, 2);
v_scopes_4018_ = lean_ctor_get(v___x_4015_, 3);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v___x_4015_, 0);
lean_dec(v_unused_4035_);
v___x_4020_ = v___x_4015_;
v_isShared_4021_ = v_isSharedCheck_4034_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_scopes_4018_);
lean_inc(v_ctx_4017_);
lean_inc(v_imported_4016_);
lean_dec(v___x_4015_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4034_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = l_Lean_Name_eraseMacroScopes(v_val_4010_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_imported_4016_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_ctx_4017_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_scopes_4018_);
v___x_4024_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v_id_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_id_4025_ = l_Lean_MacroScopesView_review(v___x_4024_);
v___x_4026_ = l_Lean_SourceInfo_fromRef(v_src_4013_, v_canonical_4011_);
lean_dec(v_src_4013_);
v___x_4027_ = 1;
v___x_4028_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_4010_, v___x_4027_);
v___x_4029_ = lean_string_utf8_byte_size(v___x_4028_);
v___x_4030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4028_);
lean_ctor_set(v___x_4030_, 1, v___x_4012_);
lean_ctor_set(v___x_4030_, 2, v___x_4029_);
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4026_);
lean_ctor_set(v___x_4032_, 1, v___x_4030_);
lean_ctor_set(v___x_4032_, 2, v_id_4025_);
lean_ctor_set(v___x_4032_, 3, v___x_4031_);
return v___x_4032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4036_, lean_object* v_val_4037_, lean_object* v_canonical_4038_){
_start:
{
uint8_t v_canonical_boxed_4039_; lean_object* v_res_4040_; 
v_canonical_boxed_4039_ = lean_unbox(v_canonical_4038_);
v_res_4040_ = l_Lean_HygieneInfo_mkIdent(v_s_4036_, v_val_4037_, v_canonical_boxed_4039_);
lean_dec(v_s_4036_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4041_, lean_object* v_inst_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = lean_apply_1(v_inst_4041_, v_a_4043_);
v___x_4045_ = lean_apply_1(v_inst_4042_, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4046_, lean_object* v_inst_4047_){
_start:
{
lean_object* v___f_4048_; 
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4048_, 0, v_inst_4046_);
lean_closure_set(v___f_4048_, 1, v_inst_4047_);
return v___f_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4049_, lean_object* v_k_4050_, lean_object* v_k_x27_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_){
_start:
{
lean_object* v___f_4054_; 
v___f_4054_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4054_, 0, v_inst_4052_);
lean_closure_set(v___f_4054_, 1, v_inst_4053_);
return v___f_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4055_, lean_object* v_k_4056_, lean_object* v_k_x27_4057_, lean_object* v_inst_4058_, lean_object* v_inst_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4055_, v_k_4056_, v_k_x27_4057_, v_inst_4058_, v_inst_4059_);
lean_dec(v_k_x27_4057_);
lean_dec(v_k_4056_);
return v_res_4060_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4069_ = l_Lean_mkCIdent(v___x_4068_);
return v___x_4069_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4075_ = l_Lean_mkCIdent(v___x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4076_){
_start:
{
if (v_x_4076_ == 0)
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4077_;
}
else
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4079_){
_start:
{
uint8_t v_x_85__boxed_4080_; lean_object* v_res_4081_; 
v_x_85__boxed_4080_ = lean_unbox(v_x_4079_);
v_res_4081_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4080_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4084_){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_box(2);
v___x_4086_ = l_Lean_Syntax_mkCharLit(v_val_4084_, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4087_){
_start:
{
uint32_t v_val_boxed_4088_; lean_object* v_res_4089_; 
v_val_boxed_4088_ = lean_unbox_uint32(v_val_4087_);
lean_dec(v_val_4087_);
v_res_4089_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4088_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4092_){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4093_ = lean_box(2);
v___x_4094_ = l_Lean_Syntax_mkStrLit(v_val_4092_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4097_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = l_Nat_reprFast(v_n_4097_);
v___x_4099_ = lean_box(2);
v___x_4100_ = l_Lean_Syntax_mkNumLit(v___x_4098_, v___x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4108_){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4109_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4110_ = lean_substring_tostring(v_s_4108_);
v___x_4111_ = lean_box(2);
v___x_4112_ = l_Lean_Syntax_mkStrLit(v___x_4110_, v___x_4111_);
v___x_4113_ = lean_unsigned_to_nat(1u);
v___x_4114_ = lean_mk_empty_array_with_capacity(v___x_4113_);
v___x_4115_ = lean_array_push(v___x_4114_, v___x_4112_);
v___x_4116_ = l_Lean_Syntax_mkCApp(v___x_4109_, v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4119_, lean_object* v_x_4120_){
_start:
{
switch(lean_obj_tag(v_x_4120_))
{
case 0:
{
uint8_t v___x_4121_; 
v___x_4121_ = l_List_isEmpty___redArg(v_acc_4119_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4122_, 0, v_acc_4119_);
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; 
lean_dec(v_acc_4119_);
v___x_4123_ = lean_box(0);
return v___x_4123_;
}
}
case 1:
{
lean_object* v_pre_4124_; lean_object* v_str_4125_; lean_object* v_val_4127_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_pre_4124_ = lean_ctor_get(v_x_4120_, 0);
lean_inc(v_pre_4124_);
v_str_4125_ = lean_ctor_get(v_x_4120_, 1);
lean_inc_ref(v_str_4125_);
lean_dec_ref_known(v_x_4120_, 2);
v___x_4130_ = lean_unsigned_to_nat(0u);
v___x_4131_ = lean_string_utf8_byte_size(v_str_4125_);
v___x_4132_ = lean_nat_dec_lt(v___x_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4133_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4134_ = lean_string_append(v___x_4133_, v_str_4125_);
lean_dec_ref(v_str_4125_);
v___x_4135_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4136_ = lean_string_append(v___x_4134_, v___x_4135_);
v_val_4127_ = v___x_4136_;
goto v___jp_4126_;
}
else
{
lean_object* v___f_4137_; uint8_t v___y_4139_; lean_object* v___f_4146_; uint32_t v___y_4153_; uint32_t v___y_4158_; uint8_t v___y_4159_; uint8_t v_c_4173_; uint8_t v___x_4182_; uint8_t v___x_4183_; 
v___f_4137_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4146_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4173_ = lean_string_get_byte_fast(v_str_4125_, v___x_4130_);
v___x_4182_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4183_ = lean_uint8_dec_le(v___x_4182_, v_c_4173_);
if (v___x_4183_ == 0)
{
goto v___jp_4177_;
}
else
{
uint8_t v___x_4184_; uint8_t v___x_4185_; 
v___x_4184_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4185_ = lean_uint8_dec_le(v_c_4173_, v___x_4184_);
if (v___x_4185_ == 0)
{
goto v___jp_4177_;
}
else
{
goto v___jp_4170_;
}
}
v___jp_4138_:
{
if (v___y_4139_ == 0)
{
uint8_t v___x_4140_; 
lean_inc_ref(v_str_4125_);
v___x_4140_ = lean_string_any(v_str_4125_, v___f_4137_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4141_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4142_ = lean_string_append(v___x_4141_, v_str_4125_);
lean_dec_ref(v_str_4125_);
v___x_4143_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4144_ = lean_string_append(v___x_4142_, v___x_4143_);
v_val_4127_ = v___x_4144_;
goto v___jp_4126_;
}
else
{
lean_object* v___x_4145_; 
lean_dec_ref(v_str_4125_);
lean_dec(v_pre_4124_);
lean_dec(v_acc_4119_);
v___x_4145_ = lean_box(0);
return v___x_4145_;
}
}
else
{
v_val_4127_ = v_str_4125_;
goto v___jp_4126_;
}
}
v___jp_4147_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
lean_inc_ref(v_str_4125_);
v___x_4148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4148_, 0, v_str_4125_);
lean_ctor_set(v___x_4148_, 1, v___x_4130_);
lean_ctor_set(v___x_4148_, 2, v___x_4131_);
v___x_4149_ = lean_unsigned_to_nat(1u);
v___x_4150_ = lean_substring_drop(v___x_4148_, v___x_4149_);
v___x_4151_ = lean_substring_all(v___x_4150_, v___f_4146_);
v___y_4139_ = v___x_4151_;
goto v___jp_4138_;
}
v___jp_4152_:
{
uint32_t v___x_4154_; uint8_t v___x_4155_; 
v___x_4154_ = 95;
v___x_4155_ = lean_uint32_dec_eq(v___y_4153_, v___x_4154_);
if (v___x_4155_ == 0)
{
uint8_t v___x_4156_; 
v___x_4156_ = l_Lean_isLetterLike(v___y_4153_);
if (v___x_4156_ == 0)
{
v___y_4139_ = v___x_4156_;
goto v___jp_4138_;
}
else
{
goto v___jp_4147_;
}
}
else
{
goto v___jp_4147_;
}
}
v___jp_4157_:
{
if (v___y_4159_ == 0)
{
uint32_t v___x_4160_; uint8_t v___x_4161_; 
v___x_4160_ = 97;
v___x_4161_ = lean_uint32_dec_le(v___x_4160_, v___y_4158_);
if (v___x_4161_ == 0)
{
v___y_4153_ = v___y_4158_;
goto v___jp_4152_;
}
else
{
uint32_t v___x_4162_; uint8_t v___x_4163_; 
v___x_4162_ = 122;
v___x_4163_ = lean_uint32_dec_le(v___y_4158_, v___x_4162_);
if (v___x_4163_ == 0)
{
v___y_4153_ = v___y_4158_;
goto v___jp_4152_;
}
else
{
goto v___jp_4147_;
}
}
}
else
{
goto v___jp_4147_;
}
}
v___jp_4164_:
{
uint32_t v___x_4165_; uint32_t v___x_4166_; uint8_t v___x_4167_; 
v___x_4165_ = lean_string_utf8_get(v_str_4125_, v___x_4130_);
v___x_4166_ = 65;
v___x_4167_ = lean_uint32_dec_le(v___x_4166_, v___x_4165_);
if (v___x_4167_ == 0)
{
v___y_4158_ = v___x_4165_;
v___y_4159_ = v___x_4167_;
goto v___jp_4157_;
}
else
{
uint32_t v___x_4168_; uint8_t v___x_4169_; 
v___x_4168_ = 90;
v___x_4169_ = lean_uint32_dec_le(v___x_4165_, v___x_4168_);
v___y_4158_ = v___x_4165_;
v___y_4159_ = v___x_4169_;
goto v___jp_4157_;
}
}
v___jp_4170_:
{
lean_object* v___x_4171_; uint8_t v___x_4172_; 
v___x_4171_ = lean_unsigned_to_nat(1u);
v___x_4172_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4125_, v___x_4171_);
if (v___x_4172_ == 0)
{
goto v___jp_4164_;
}
else
{
v___y_4139_ = v___x_4172_;
goto v___jp_4138_;
}
}
v___jp_4174_:
{
uint8_t v___x_4175_; uint8_t v___x_4176_; 
v___x_4175_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4176_ = lean_uint8_dec_eq(v_c_4173_, v___x_4175_);
if (v___x_4176_ == 0)
{
goto v___jp_4164_;
}
else
{
goto v___jp_4170_;
}
}
v___jp_4177_:
{
uint8_t v___x_4178_; uint8_t v___x_4179_; 
v___x_4178_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4179_ = lean_uint8_dec_le(v___x_4178_, v_c_4173_);
if (v___x_4179_ == 0)
{
goto v___jp_4174_;
}
else
{
uint8_t v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4181_ = lean_uint8_dec_le(v_c_4173_, v___x_4180_);
if (v___x_4181_ == 0)
{
goto v___jp_4174_;
}
else
{
goto v___jp_4170_;
}
}
}
}
v___jp_4126_:
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4128_, 0, v_val_4127_);
lean_ctor_set(v___x_4128_, 1, v_acc_4119_);
v_acc_4119_ = v___x_4128_;
v_x_4120_ = v_pre_4124_;
goto _start;
}
}
default: 
{
lean_object* v___x_4186_; 
lean_dec_ref_known(v_x_4120_, 2);
lean_dec(v_acc_4119_);
v___x_4186_ = lean_box(0);
return v___x_4186_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4194_ = l_Lean_mkCIdent(v___x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4205_){
_start:
{
switch(lean_obj_tag(v_x_4205_))
{
case 0:
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4206_;
}
case 1:
{
lean_object* v_pre_4207_; lean_object* v_str_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_pre_4207_ = lean_ctor_get(v_x_4205_, 0);
lean_inc(v_pre_4207_);
v_str_4208_ = lean_ctor_get(v_x_4205_, 1);
lean_inc_ref(v_str_4208_);
lean_dec_ref_known(v_x_4205_, 2);
v___x_4209_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4210_ = l_Lean_quoteNameMk(v_pre_4207_);
v___x_4211_ = lean_box(2);
v___x_4212_ = l_Lean_Syntax_mkStrLit(v_str_4208_, v___x_4211_);
v___x_4213_ = lean_unsigned_to_nat(2u);
v___x_4214_ = lean_mk_empty_array_with_capacity(v___x_4213_);
v___x_4215_ = lean_array_push(v___x_4214_, v___x_4210_);
v___x_4216_ = lean_array_push(v___x_4215_, v___x_4212_);
v___x_4217_ = l_Lean_Syntax_mkCApp(v___x_4209_, v___x_4216_);
return v___x_4217_;
}
default: 
{
lean_object* v_pre_4218_; lean_object* v_i_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v_pre_4218_ = lean_ctor_get(v_x_4205_, 0);
lean_inc(v_pre_4218_);
v_i_4219_ = lean_ctor_get(v_x_4205_, 1);
lean_inc(v_i_4219_);
lean_dec_ref_known(v_x_4205_, 2);
v___x_4220_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4221_ = l_Lean_quoteNameMk(v_pre_4218_);
v___x_4222_ = l_Nat_reprFast(v_i_4219_);
v___x_4223_ = lean_box(2);
v___x_4224_ = l_Lean_Syntax_mkNumLit(v___x_4222_, v___x_4223_);
v___x_4225_ = lean_unsigned_to_nat(2u);
v___x_4226_ = lean_mk_empty_array_with_capacity(v___x_4225_);
v___x_4227_ = lean_array_push(v___x_4226_, v___x_4221_);
v___x_4228_ = lean_array_push(v___x_4227_, v___x_4224_);
v___x_4229_ = l_Lean_Syntax_mkCApp(v___x_4220_, v___x_4228_);
return v___x_4229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4236_){
_start:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_box(0);
lean_inc(v_n_4236_);
v___x_4238_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4237_, v_n_4236_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_quoteNameMk(v_n_4236_);
return v___x_4239_;
}
else
{
lean_object* v_val_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
lean_dec(v_n_4236_);
v_val_4240_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_val_4240_);
lean_dec_ref_known(v___x_4238_, 1);
v___x_4241_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4242_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4243_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4244_ = lean_string_intercalate(v___x_4243_, v_val_4240_);
v___x_4245_ = lean_string_append(v___x_4242_, v___x_4244_);
lean_dec_ref(v___x_4244_);
v___x_4246_ = lean_box(2);
v___x_4247_ = l_Lean_Syntax_mkNameLit(v___x_4245_, v___x_4246_);
v___x_4248_ = lean_unsigned_to_nat(1u);
v___x_4249_ = lean_mk_empty_array_with_capacity(v___x_4248_);
v___x_4250_ = lean_array_push(v___x_4249_, v___x_4247_);
v___x_4251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4246_);
lean_ctor_set(v___x_4251_, 1, v___x_4241_);
lean_ctor_set(v___x_4251_, 2, v___x_4250_);
return v___x_4251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4252_){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = lean_box(0);
lean_inc(v_n_4252_);
v___x_4254_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4253_, v_n_4252_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_quoteNameMk(v_n_4252_);
return v___x_4255_;
}
else
{
lean_object* v_val_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec(v_n_4252_);
v_val_4256_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_val_4256_);
lean_dec_ref_known(v___x_4254_, 1);
v___x_4257_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4258_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4259_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4260_ = lean_string_intercalate(v___x_4259_, v_val_4256_);
v___x_4261_ = lean_string_append(v___x_4258_, v___x_4260_);
lean_dec_ref(v___x_4260_);
v___x_4262_ = lean_box(2);
v___x_4263_ = l_Lean_Syntax_mkNameLit(v___x_4261_, v___x_4262_);
v___x_4264_ = lean_unsigned_to_nat(1u);
v___x_4265_ = lean_mk_empty_array_with_capacity(v___x_4264_);
v___x_4266_ = lean_array_push(v___x_4265_, v___x_4263_);
v___x_4267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4262_);
lean_ctor_set(v___x_4267_, 1, v___x_4257_);
lean_ctor_set(v___x_4267_, 2, v___x_4266_);
return v___x_4267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4275_, lean_object* v_inst_4276_, lean_object* v_x_4277_){
_start:
{
lean_object* v_fst_4278_; lean_object* v_snd_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_fst_4278_ = lean_ctor_get(v_x_4277_, 0);
lean_inc(v_fst_4278_);
v_snd_4279_ = lean_ctor_get(v_x_4277_, 1);
lean_inc(v_snd_4279_);
lean_dec_ref(v_x_4277_);
v___x_4280_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4281_ = lean_apply_1(v_inst_4275_, v_fst_4278_);
v___x_4282_ = lean_apply_1(v_inst_4276_, v_snd_4279_);
v___x_4283_ = lean_unsigned_to_nat(2u);
v___x_4284_ = lean_mk_empty_array_with_capacity(v___x_4283_);
v___x_4285_ = lean_array_push(v___x_4284_, v___x_4281_);
v___x_4286_ = lean_array_push(v___x_4285_, v___x_4282_);
v___x_4287_ = l_Lean_Syntax_mkCApp(v___x_4280_, v___x_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4288_, lean_object* v_inst_4289_){
_start:
{
lean_object* v___f_4290_; 
v___f_4290_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4290_, 0, v_inst_4288_);
lean_closure_set(v___f_4290_, 1, v_inst_4289_);
return v___f_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4291_, lean_object* v_00_u03b2_4292_, lean_object* v_inst_4293_, lean_object* v_inst_4294_){
_start:
{
lean_object* v___f_4295_; 
v___f_4295_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4295_, 0, v_inst_4293_);
lean_closure_set(v___f_4295_, 1, v_inst_4294_);
return v___f_4295_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4302_ = l_Lean_mkCIdent(v___x_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4307_, lean_object* v_x_4308_){
_start:
{
if (lean_obj_tag(v_x_4308_) == 0)
{
lean_object* v___x_4309_; 
lean_dec_ref(v_inst_4307_);
v___x_4309_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4309_;
}
else
{
lean_object* v_head_4310_; lean_object* v_tail_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_head_4310_ = lean_ctor_get(v_x_4308_, 0);
lean_inc(v_head_4310_);
v_tail_4311_ = lean_ctor_get(v_x_4308_, 1);
lean_inc(v_tail_4311_);
lean_dec_ref_known(v_x_4308_, 2);
v___x_4312_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4307_);
v___x_4313_ = lean_apply_1(v_inst_4307_, v_head_4310_);
v___x_4314_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4307_, v_tail_4311_);
v___x_4315_ = lean_unsigned_to_nat(2u);
v___x_4316_ = lean_mk_empty_array_with_capacity(v___x_4315_);
v___x_4317_ = lean_array_push(v___x_4316_, v___x_4313_);
v___x_4318_ = lean_array_push(v___x_4317_, v___x_4314_);
v___x_4319_ = l_Lean_Syntax_mkCApp(v___x_4312_, v___x_4318_);
return v___x_4319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4320_, lean_object* v_inst_4321_, lean_object* v_x_4322_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4321_, v_x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4324_, v_a_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4327_, lean_object* v_inst_4328_, lean_object* v_a_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4328_, v_a_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4332_, 0, lean_box(0));
lean_closure_set(v___x_4332_, 1, v_inst_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4333_, lean_object* v_inst_4334_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4335_, 0, lean_box(0));
lean_closure_set(v___x_4335_, 1, v_inst_4334_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4338_, lean_object* v_xs_4339_, lean_object* v_i_4340_, lean_object* v_args_4341_){
_start:
{
lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4342_ = lean_array_get_size(v_xs_4339_);
v___x_4343_ = lean_nat_dec_lt(v_i_4340_, v___x_4342_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
lean_dec(v_i_4340_);
lean_dec_ref(v_inst_4338_);
v___x_4344_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4345_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4346_ = l_Nat_reprFast(v___x_4342_);
v___x_4347_ = lean_string_append(v___x_4345_, v___x_4346_);
lean_dec_ref(v___x_4346_);
v___x_4348_ = l_Lean_Name_mkStr2(v___x_4344_, v___x_4347_);
v___x_4349_ = l_Lean_Syntax_mkCApp(v___x_4348_, v_args_4341_);
return v___x_4349_;
}
else
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4350_ = lean_unsigned_to_nat(1u);
v___x_4351_ = lean_nat_add(v_i_4340_, v___x_4350_);
v___x_4352_ = lean_array_fget_borrowed(v_xs_4339_, v_i_4340_);
lean_dec(v_i_4340_);
lean_inc_ref(v_inst_4338_);
lean_inc(v___x_4352_);
v___x_4353_ = lean_apply_1(v_inst_4338_, v___x_4352_);
v___x_4354_ = lean_array_push(v_args_4341_, v___x_4353_);
v_i_4340_ = v___x_4351_;
v_args_4341_ = v___x_4354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4356_, lean_object* v_xs_4357_, lean_object* v_i_4358_, lean_object* v_args_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4356_, v_xs_4357_, v_i_4358_, v_args_4359_);
lean_dec_ref(v_xs_4357_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4361_, lean_object* v_inst_4362_, lean_object* v_xs_4363_, lean_object* v_i_4364_, lean_object* v_args_4365_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4362_, v_xs_4363_, v_i_4364_, v_args_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4367_, lean_object* v_inst_4368_, lean_object* v_xs_4369_, lean_object* v_i_4370_, lean_object* v_args_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4367_, v_inst_4368_, v_xs_4369_, v_i_4370_, v_args_4371_);
lean_dec_ref(v_xs_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4377_, lean_object* v_xs_4378_){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4379_ = lean_array_get_size(v_xs_4378_);
v___x_4380_ = lean_unsigned_to_nat(8u);
v___x_4381_ = lean_nat_dec_le(v___x_4379_, v___x_4380_);
if (v___x_4381_ == 0)
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4382_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4383_ = lean_array_to_list(v_xs_4378_);
v___x_4384_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4377_, v___x_4383_);
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = lean_mk_empty_array_with_capacity(v___x_4385_);
v___x_4387_ = lean_array_push(v___x_4386_, v___x_4384_);
v___x_4388_ = l_Lean_Syntax_mkCApp(v___x_4382_, v___x_4387_);
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = lean_unsigned_to_nat(0u);
v___x_4390_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4391_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4377_, v_xs_4378_, v___x_4389_, v___x_4390_);
lean_dec_ref(v_xs_4378_);
return v___x_4391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4392_, lean_object* v_inst_4393_, lean_object* v_xs_4394_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4393_, v_xs_4394_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4396_, lean_object* v_xs_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4396_, v_xs_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4399_, lean_object* v_inst_4400_, lean_object* v_xs_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4400_, v_xs_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4403_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4404_, 0, lean_box(0));
lean_closure_set(v___x_4404_, 1, v_inst_4403_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4405_, lean_object* v_inst_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4407_, 0, lean_box(0));
lean_closure_set(v___x_4407_, 1, v_inst_4406_);
return v___x_4407_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4414_ = l_Lean_mkIdent(v___x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4419_, lean_object* v_x_4420_){
_start:
{
if (lean_obj_tag(v_x_4420_) == 0)
{
lean_object* v___x_4421_; 
lean_dec_ref(v_inst_4419_);
v___x_4421_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4421_;
}
else
{
lean_object* v_val_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v_val_4422_ = lean_ctor_get(v_x_4420_, 0);
lean_inc(v_val_4422_);
lean_dec_ref_known(v_x_4420_, 1);
v___x_4423_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4424_ = lean_apply_1(v_inst_4419_, v_val_4422_);
v___x_4425_ = lean_unsigned_to_nat(1u);
v___x_4426_ = lean_mk_empty_array_with_capacity(v___x_4425_);
v___x_4427_ = lean_array_push(v___x_4426_, v___x_4424_);
v___x_4428_ = l_Lean_Syntax_mkCApp(v___x_4423_, v___x_4427_);
return v___x_4428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4429_){
_start:
{
lean_object* v___f_4430_; 
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4430_, 0, v_inst_4429_);
return v___f_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4431_, lean_object* v_inst_4432_){
_start:
{
lean_object* v___f_4433_; 
v___f_4433_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4433_, 0, v_inst_4432_);
return v___f_4433_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4434_, lean_object* v_k_4435_){
_start:
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4437_ = lean_name_eq(v_k_4435_, v___x_4436_);
if (v___x_4437_ == 0)
{
uint8_t v___x_4438_; 
v___x_4438_ = 1;
return v___x_4438_;
}
else
{
return v___x_4434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4439_, lean_object* v_k_4440_){
_start:
{
uint8_t v___x_442__boxed_4441_; uint8_t v_res_4442_; lean_object* v_r_4443_; 
v___x_442__boxed_4441_ = lean_unbox(v___x_4439_);
v_res_4442_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4441_, v_k_4440_);
lean_dec(v_k_4440_);
v_r_4443_ = lean_box(v_res_4442_);
return v_r_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_methods_4448_; lean_object* v_quotContext_4449_; lean_object* v_currMacroScope_4450_; lean_object* v_currRecDepth_4451_; lean_object* v_maxRecDepth_4452_; lean_object* v_ref_4453_; uint8_t v___x_4454_; 
v_methods_4448_ = lean_ctor_get(v_a_4446_, 0);
v_quotContext_4449_ = lean_ctor_get(v_a_4446_, 1);
v_currMacroScope_4450_ = lean_ctor_get(v_a_4446_, 2);
v_currRecDepth_4451_ = lean_ctor_get(v_a_4446_, 3);
v_maxRecDepth_4452_ = lean_ctor_get(v_a_4446_, 4);
v_ref_4453_ = lean_ctor_get(v_a_4446_, 5);
v___x_4454_ = lean_nat_dec_eq(v_currRecDepth_4451_, v_maxRecDepth_4452_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4455_ = lean_box(v___x_4454_);
v___f_4456_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4456_, 0, v___x_4455_);
v___x_4457_ = lean_unsigned_to_nat(1u);
v___x_4458_ = lean_nat_add(v_currRecDepth_4451_, v___x_4457_);
lean_inc(v_ref_4453_);
lean_inc(v_maxRecDepth_4452_);
lean_inc(v_currMacroScope_4450_);
lean_inc(v_quotContext_4449_);
lean_inc(v_methods_4448_);
v___x_4459_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4459_, 0, v_methods_4448_);
lean_ctor_set(v___x_4459_, 1, v_quotContext_4449_);
lean_ctor_set(v___x_4459_, 2, v_currMacroScope_4450_);
lean_ctor_set(v___x_4459_, 3, v___x_4458_);
lean_ctor_set(v___x_4459_, 4, v_maxRecDepth_4452_);
lean_ctor_set(v___x_4459_, 5, v_ref_4453_);
lean_inc_ref(v___x_4459_);
v___x_4460_ = l_Lean_expandMacros(v_stx_4445_, v___f_4456_, v___x_4459_, v_a_4447_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4474_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_a_4462_ = lean_ctor_get(v___x_4460_, 1);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4464_ = v___x_4460_;
v_isShared_4465_ = v_isSharedCheck_4474_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4474_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; uint8_t v___x_4467_; 
v___x_4466_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4461_);
v___x_4467_ = l_Lean_Syntax_isOfKind(v_a_4461_, v___x_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_del_object(v___x_4464_);
v___x_4468_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4469_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4461_, v___x_4468_, v___x_4459_, v_a_4462_);
lean_dec_ref_known(v___x_4459_, 6);
lean_dec(v_a_4461_);
return v___x_4469_;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4472_; 
lean_dec_ref_known(v___x_4459_, 6);
v___x_4470_ = l_Lean_TSyntax_getNat(v_a_4461_);
lean_dec(v_a_4461_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4470_);
v___x_4472_ = v___x_4464_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v_a_4462_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref_known(v___x_4459_, 6);
v_a_4475_ = lean_ctor_get(v___x_4460_, 0);
v_a_4476_ = lean_ctor_get(v___x_4460_, 1);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4460_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_inc(v_a_4475_);
lean_dec(v___x_4460_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4475_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4484_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v_stx_4445_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
lean_ctor_set(v___x_4486_, 1, v_a_4447_);
return v___x_4486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Lean_evalPrec(v_stx_4487_, v_a_4488_, v_a_4489_);
lean_dec_ref(v_a_4488_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
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
v___x_4515_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_evalPrio(v_stx_4534_, v_a_4535_, v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
if (lean_obj_tag(v_x_4538_) == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_unsigned_to_nat(1000u);
v___x_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
lean_ctor_set(v___x_4542_, 1, v_a_4540_);
return v___x_4542_;
}
else
{
lean_object* v_val_4543_; lean_object* v___x_4544_; 
v_val_4543_ = lean_ctor_get(v_x_4538_, 0);
lean_inc(v_val_4543_);
lean_dec_ref_known(v_x_4538_, 1);
v___x_4544_ = l_Lean_evalPrio(v_val_4543_, v_a_4539_, v_a_4540_);
return v___x_4544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Lean_evalOptPrio(v_x_4545_, v_a_4546_, v_a_4547_);
lean_dec_ref(v_a_4546_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4549_, lean_object* v_x1_4550_, lean_object* v_x2_4551_){
_start:
{
lean_object* v_fst_4552_; uint8_t v___x_4553_; 
v_fst_4552_ = lean_ctor_get(v_x1_4550_, 0);
v___x_4553_ = lean_unbox(v_fst_4552_);
if (v___x_4553_ == 0)
{
lean_object* v_snd_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_x2_4551_);
v_snd_4554_ = lean_ctor_get(v_x1_4550_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x1_4550_);
if (v_isSharedCheck_4562_ == 0)
{
lean_object* v_unused_4563_; 
v_unused_4563_ = lean_ctor_get(v_x1_4550_, 0);
lean_dec(v_unused_4563_);
v___x_4556_ = v_x1_4550_;
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_snd_4554_);
lean_dec(v_x1_4550_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v___x_4560_; 
v___x_4558_ = lean_box(v___x_4549_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 0, v___x_4558_);
v___x_4560_ = v___x_4556_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_snd_4554_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
else
{
lean_object* v_snd_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4574_; 
v_snd_4564_ = lean_ctor_get(v_x1_4550_, 1);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_x1_4550_);
if (v_isSharedCheck_4574_ == 0)
{
lean_object* v_unused_4575_; 
v_unused_4575_ = lean_ctor_get(v_x1_4550_, 0);
lean_dec(v_unused_4575_);
v___x_4566_ = v_x1_4550_;
v_isShared_4567_ = v_isSharedCheck_4574_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_snd_4564_);
lean_dec(v_x1_4550_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4574_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
uint8_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
v___x_4568_ = 0;
v___x_4569_ = lean_array_push(v_snd_4564_, v_x2_4551_);
v___x_4570_ = lean_box(v___x_4568_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 1, v___x_4569_);
lean_ctor_set(v___x_4566_, 0, v___x_4570_);
v___x_4572_ = v___x_4566_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v___x_4569_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4576_, lean_object* v_x1_4577_, lean_object* v_x2_4578_){
_start:
{
uint8_t v___x_87__boxed_4579_; lean_object* v_res_4580_; 
v___x_87__boxed_4579_ = lean_unbox(v___x_4576_);
v_res_4580_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4579_, v_x1_4577_, v_x2_4578_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4602_){
_start:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; uint8_t v___x_4607_; 
v___x_4603_ = lean_unsigned_to_nat(0u);
v___x_4604_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4605_ = lean_array_get_size(v_as_4602_);
v___x_4606_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4607_ = lean_nat_dec_lt(v___x_4603_, v___x_4605_);
if (v___x_4607_ == 0)
{
lean_dec_ref(v_as_4602_);
return v___x_4604_;
}
else
{
lean_object* v___x_4608_; lean_object* v___f_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; size_t v___x_4612_; size_t v___x_4613_; lean_object* v___x_4614_; lean_object* v_snd_4615_; 
v___x_4608_ = lean_box(v___x_4607_);
v___f_4609_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4609_, 0, v___x_4608_);
v___x_4610_ = lean_box(v___x_4607_);
v___x_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
lean_ctor_set(v___x_4611_, 1, v___x_4604_);
v___x_4612_ = ((size_t)0ULL);
v___x_4613_ = lean_usize_of_nat(v___x_4605_);
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4606_, v___f_4609_, v_as_4602_, v___x_4612_, v___x_4613_, v___x_4611_);
v_snd_4615_ = lean_ctor_get(v___x_4614_, 1);
lean_inc(v_snd_4615_);
lean_dec(v___x_4614_);
return v_snd_4615_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4616_, lean_object* v_as_4617_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; 
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4620_ = lean_array_get_size(v_as_4617_);
v___x_4621_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4622_ = lean_nat_dec_lt(v___x_4618_, v___x_4620_);
if (v___x_4622_ == 0)
{
lean_dec_ref(v_as_4617_);
return v___x_4619_;
}
else
{
lean_object* v___x_4623_; lean_object* v___f_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; size_t v___x_4627_; size_t v___x_4628_; lean_object* v___x_4629_; lean_object* v_snd_4630_; 
v___x_4623_ = lean_box(v___x_4622_);
v___f_4624_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4624_, 0, v___x_4623_);
v___x_4625_ = lean_box(v___x_4622_);
v___x_4626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
lean_ctor_set(v___x_4626_, 1, v___x_4619_);
v___x_4627_ = ((size_t)0ULL);
v___x_4628_ = lean_usize_of_nat(v___x_4620_);
v___x_4629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4621_, v___f_4624_, v_as_4617_, v___x_4627_, v___x_4628_, v___x_4626_);
v_snd_4630_ = lean_ctor_get(v___x_4629_, 1);
lean_inc(v_snd_4630_);
lean_dec(v___x_4629_);
return v_snd_4630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4631_, lean_object* v_inst_4632_, lean_object* v_a_4633_, lean_object* v_p_4634_, lean_object* v_acc_4635_, lean_object* v_stx_4636_, uint8_t v_____do__lift_4637_){
_start:
{
if (v_____do__lift_4637_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
lean_dec(v_stx_4636_);
v___x_4646_ = lean_unsigned_to_nat(2u);
v___x_4647_ = lean_nat_add(v_i_4631_, v___x_4646_);
v___x_4648_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4632_, v_a_4633_, v_p_4634_, v___x_4647_, v_acc_4635_);
return v___x_4648_;
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v___x_4649_ = lean_array_get_size(v_acc_4635_);
v___x_4650_ = lean_unsigned_to_nat(0u);
v___x_4651_ = lean_nat_dec_eq(v___x_4649_, v___x_4650_);
if (v___x_4651_ == 0)
{
uint8_t v___x_4652_; 
v___x_4652_ = lean_nat_dec_eq(v_i_4631_, v___x_4650_);
if (v___x_4652_ == 0)
{
goto v___jp_4638_;
}
else
{
if (v___x_4651_ == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4653_ = lean_unsigned_to_nat(2u);
v___x_4654_ = lean_nat_add(v_i_4631_, v___x_4653_);
v___x_4655_ = lean_array_push(v_acc_4635_, v_stx_4636_);
v___x_4656_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4632_, v_a_4633_, v_p_4634_, v___x_4654_, v___x_4655_);
return v___x_4656_;
}
else
{
goto v___jp_4638_;
}
}
}
else
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4657_ = lean_unsigned_to_nat(2u);
v___x_4658_ = lean_nat_add(v_i_4631_, v___x_4657_);
v___x_4659_ = lean_array_push(v_acc_4635_, v_stx_4636_);
v___x_4660_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4632_, v_a_4633_, v_p_4634_, v___x_4658_, v___x_4659_);
return v___x_4660_;
}
}
v___jp_4638_:
{
lean_object* v___x_4639_; lean_object* v_sepStx_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4639_ = lean_nat_pred(v_i_4631_);
v_sepStx_4640_ = lean_array_fget_borrowed(v_a_4633_, v___x_4639_);
lean_dec(v___x_4639_);
v___x_4641_ = lean_unsigned_to_nat(2u);
v___x_4642_ = lean_nat_add(v_i_4631_, v___x_4641_);
lean_inc(v_sepStx_4640_);
v___x_4643_ = lean_array_push(v_acc_4635_, v_sepStx_4640_);
v___x_4644_ = lean_array_push(v___x_4643_, v_stx_4636_);
v___x_4645_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4632_, v_a_4633_, v_p_4634_, v___x_4642_, v___x_4644_);
return v___x_4645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4661_, lean_object* v_inst_4662_, lean_object* v_a_4663_, lean_object* v_p_4664_, lean_object* v_acc_4665_, lean_object* v_stx_4666_, lean_object* v_____do__lift_4667_){
_start:
{
uint8_t v_____do__lift_208__boxed_4668_; lean_object* v_res_4669_; 
v_____do__lift_208__boxed_4668_ = lean_unbox(v_____do__lift_4667_);
v_res_4669_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4661_, v_inst_4662_, v_a_4663_, v_p_4664_, v_acc_4665_, v_stx_4666_, v_____do__lift_208__boxed_4668_);
lean_dec(v_i_4661_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4670_, lean_object* v_a_4671_, lean_object* v_p_4672_, lean_object* v_i_4673_, lean_object* v_acc_4674_){
_start:
{
lean_object* v_toApplicative_4675_; lean_object* v_toBind_4676_; lean_object* v_toPure_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v_toApplicative_4675_ = lean_ctor_get(v_inst_4670_, 0);
v_toBind_4676_ = lean_ctor_get(v_inst_4670_, 1);
lean_inc(v_toBind_4676_);
v_toPure_4677_ = lean_ctor_get(v_toApplicative_4675_, 1);
v___x_4678_ = lean_array_get_size(v_a_4671_);
v___x_4679_ = lean_nat_dec_lt(v_i_4673_, v___x_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; 
lean_inc(v_toPure_4677_);
lean_dec(v_toBind_4676_);
lean_dec(v_i_4673_);
lean_dec(v_p_4672_);
lean_dec_ref(v_a_4671_);
lean_dec_ref(v_inst_4670_);
v___x_4680_ = lean_apply_2(v_toPure_4677_, lean_box(0), v_acc_4674_);
return v___x_4680_;
}
else
{
lean_object* v_stx_4681_; lean_object* v___f_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v_stx_4681_ = lean_array_fget(v_a_4671_, v_i_4673_);
lean_inc(v_stx_4681_);
lean_inc(v_p_4672_);
v___f_4682_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4682_, 0, v_i_4673_);
lean_closure_set(v___f_4682_, 1, v_inst_4670_);
lean_closure_set(v___f_4682_, 2, v_a_4671_);
lean_closure_set(v___f_4682_, 3, v_p_4672_);
lean_closure_set(v___f_4682_, 4, v_acc_4674_);
lean_closure_set(v___f_4682_, 5, v_stx_4681_);
v___x_4683_ = lean_apply_1(v_p_4672_, v_stx_4681_);
v___x_4684_ = lean_apply_4(v_toBind_4676_, lean_box(0), lean_box(0), v___x_4683_, v___f_4682_);
return v___x_4684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4685_, lean_object* v_inst_4686_, lean_object* v_a_4687_, lean_object* v_p_4688_, lean_object* v_i_4689_, lean_object* v_acc_4690_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4686_, v_a_4687_, v_p_4688_, v_i_4689_, v_acc_4690_);
return v___x_4691_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4692_, lean_object* v_a_4693_, lean_object* v_p_4694_){
_start:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4697_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4692_, v_a_4693_, v_p_4694_, v___x_4695_, v___x_4696_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4698_, lean_object* v_inst_4699_, lean_object* v_a_4700_, lean_object* v_p_4701_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Array_filterSepElemsM___redArg(v_inst_4699_, v_a_4700_, v_p_4701_);
return v___x_4702_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4703_, lean_object* v_x_4704_){
_start:
{
lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4705_ = lean_apply_1(v_p_4703_, v_x_4704_);
v___x_4706_ = lean_unbox(v___x_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4707_, lean_object* v_x_4708_){
_start:
{
uint8_t v_res_4709_; lean_object* v_r_4710_; 
v_res_4709_ = l_Array_filterSepElems___lam__0(v_p_4707_, v_x_4708_);
v_r_4710_ = lean_box(v_res_4709_);
return v_r_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4711_, lean_object* v_p_4712_, lean_object* v_i_4713_, lean_object* v_acc_4714_){
_start:
{
lean_object* v___x_4715_; uint8_t v___x_4716_; 
v___x_4715_ = lean_array_get_size(v_a_4711_);
v___x_4716_ = lean_nat_dec_lt(v_i_4713_, v___x_4715_);
if (v___x_4716_ == 0)
{
lean_dec(v_i_4713_);
lean_dec_ref(v_p_4712_);
return v_acc_4714_;
}
else
{
lean_object* v_stx_4717_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v_stx_4717_ = lean_array_fget_borrowed(v_a_4711_, v_i_4713_);
lean_inc_ref(v_p_4712_);
lean_inc(v_stx_4717_);
v___x_4726_ = lean_apply_1(v_p_4712_, v_stx_4717_);
v___x_4727_ = lean_unbox(v___x_4726_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_unsigned_to_nat(2u);
v___x_4729_ = lean_nat_add(v_i_4713_, v___x_4728_);
lean_dec(v_i_4713_);
v_i_4713_ = v___x_4729_;
goto _start;
}
else
{
lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4731_ = lean_array_get_size(v_acc_4714_);
v___x_4732_ = lean_unsigned_to_nat(0u);
v___x_4733_ = lean_nat_dec_eq(v___x_4731_, v___x_4732_);
if (v___x_4733_ == 0)
{
uint8_t v___x_4734_; 
v___x_4734_ = lean_nat_dec_eq(v_i_4713_, v___x_4732_);
if (v___x_4734_ == 0)
{
goto v___jp_4718_;
}
else
{
if (v___x_4733_ == 0)
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4735_ = lean_unsigned_to_nat(2u);
v___x_4736_ = lean_nat_add(v_i_4713_, v___x_4735_);
lean_dec(v_i_4713_);
lean_inc(v_stx_4717_);
v___x_4737_ = lean_array_push(v_acc_4714_, v_stx_4717_);
v_i_4713_ = v___x_4736_;
v_acc_4714_ = v___x_4737_;
goto _start;
}
else
{
goto v___jp_4718_;
}
}
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4739_ = lean_unsigned_to_nat(2u);
v___x_4740_ = lean_nat_add(v_i_4713_, v___x_4739_);
lean_dec(v_i_4713_);
lean_inc(v_stx_4717_);
v___x_4741_ = lean_array_push(v_acc_4714_, v_stx_4717_);
v_i_4713_ = v___x_4740_;
v_acc_4714_ = v___x_4741_;
goto _start;
}
}
v___jp_4718_:
{
lean_object* v___x_4719_; lean_object* v_sepStx_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4719_ = lean_nat_pred(v_i_4713_);
v_sepStx_4720_ = lean_array_fget_borrowed(v_a_4711_, v___x_4719_);
lean_dec(v___x_4719_);
v___x_4721_ = lean_unsigned_to_nat(2u);
v___x_4722_ = lean_nat_add(v_i_4713_, v___x_4721_);
lean_dec(v_i_4713_);
lean_inc(v_sepStx_4720_);
v___x_4723_ = lean_array_push(v_acc_4714_, v_sepStx_4720_);
lean_inc(v_stx_4717_);
v___x_4724_ = lean_array_push(v___x_4723_, v_stx_4717_);
v_i_4713_ = v___x_4722_;
v_acc_4714_ = v___x_4724_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4743_, lean_object* v_p_4744_, lean_object* v_i_4745_, lean_object* v_acc_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4743_, v_p_4744_, v_i_4745_, v_acc_4746_);
lean_dec_ref(v_a_4743_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4748_, lean_object* v_p_4749_){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = lean_unsigned_to_nat(0u);
v___x_4751_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4752_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4748_, v_p_4749_, v___x_4750_, v___x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4753_, lean_object* v_p_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4753_, v_p_4754_);
lean_dec_ref(v_a_4753_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4756_, lean_object* v_p_4757_){
_start:
{
lean_object* v___f_4758_; lean_object* v___x_4759_; 
v___f_4758_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4758_, 0, v_p_4757_);
v___x_4759_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4756_, v___f_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4760_, lean_object* v_p_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Array_filterSepElems(v_a_4760_, v_p_4761_);
lean_dec_ref(v_a_4760_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4763_, lean_object* v_acc_4764_, lean_object* v_inst_4765_, lean_object* v_a_4766_, lean_object* v_f_4767_, lean_object* v_stx_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4763_, v_acc_4764_, v_inst_4765_, v_a_4766_, v_f_4767_, v_stx_4768_);
lean_dec(v_i_4763_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4770_, lean_object* v_a_4771_, lean_object* v_f_4772_, lean_object* v_i_4773_, lean_object* v_acc_4774_){
_start:
{
lean_object* v_toApplicative_4775_; lean_object* v_toBind_4776_; lean_object* v_toPure_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; 
v_toApplicative_4775_ = lean_ctor_get(v_inst_4770_, 0);
v_toBind_4776_ = lean_ctor_get(v_inst_4770_, 1);
v_toPure_4777_ = lean_ctor_get(v_toApplicative_4775_, 1);
v___x_4778_ = lean_array_get_size(v_a_4771_);
v___x_4779_ = lean_nat_dec_lt(v_i_4773_, v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; 
lean_inc(v_toPure_4777_);
lean_dec(v_i_4773_);
lean_dec(v_f_4772_);
lean_dec_ref(v_a_4771_);
lean_dec_ref(v_inst_4770_);
v___x_4780_ = lean_apply_2(v_toPure_4777_, lean_box(0), v_acc_4774_);
return v___x_4780_;
}
else
{
lean_object* v_stx_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; uint8_t v___x_4785_; 
v_stx_4781_ = lean_array_fget_borrowed(v_a_4771_, v_i_4773_);
v___x_4782_ = lean_unsigned_to_nat(2u);
v___x_4783_ = lean_nat_mod(v_i_4773_, v___x_4782_);
v___x_4784_ = lean_unsigned_to_nat(0u);
v___x_4785_ = lean_nat_dec_eq(v___x_4783_, v___x_4784_);
lean_dec(v___x_4783_);
if (v___x_4785_ == 0)
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4786_ = lean_unsigned_to_nat(1u);
v___x_4787_ = lean_nat_add(v_i_4773_, v___x_4786_);
lean_dec(v_i_4773_);
lean_inc(v_stx_4781_);
v___x_4788_ = lean_array_push(v_acc_4774_, v_stx_4781_);
v_i_4773_ = v___x_4787_;
v_acc_4774_ = v___x_4788_;
goto _start;
}
else
{
lean_object* v___f_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
lean_inc(v_stx_4781_);
lean_inc(v_toBind_4776_);
lean_inc(v_f_4772_);
v___f_4790_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4790_, 0, v_i_4773_);
lean_closure_set(v___f_4790_, 1, v_acc_4774_);
lean_closure_set(v___f_4790_, 2, v_inst_4770_);
lean_closure_set(v___f_4790_, 3, v_a_4771_);
lean_closure_set(v___f_4790_, 4, v_f_4772_);
v___x_4791_ = lean_apply_1(v_f_4772_, v_stx_4781_);
v___x_4792_ = lean_apply_4(v_toBind_4776_, lean_box(0), lean_box(0), v___x_4791_, v___f_4790_);
return v___x_4792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4793_, lean_object* v_acc_4794_, lean_object* v_inst_4795_, lean_object* v_a_4796_, lean_object* v_f_4797_, lean_object* v_stx_4798_){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4799_ = lean_unsigned_to_nat(1u);
v___x_4800_ = lean_nat_add(v_i_4793_, v___x_4799_);
v___x_4801_ = lean_array_push(v_acc_4794_, v_stx_4798_);
v___x_4802_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4795_, v_a_4796_, v_f_4797_, v___x_4800_, v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4803_, lean_object* v_inst_4804_, lean_object* v_a_4805_, lean_object* v_f_4806_, lean_object* v_i_4807_, lean_object* v_acc_4808_){
_start:
{
lean_object* v___x_4809_; 
v___x_4809_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4804_, v_a_4805_, v_f_4806_, v_i_4807_, v_acc_4808_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4810_, lean_object* v_a_4811_, lean_object* v_f_4812_){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = lean_unsigned_to_nat(0u);
v___x_4814_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4815_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4810_, v_a_4811_, v_f_4812_, v___x_4813_, v___x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4816_, lean_object* v_inst_4817_, lean_object* v_a_4818_, lean_object* v_f_4819_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Array_mapSepElemsM___redArg(v_inst_4817_, v_a_4818_, v_f_4819_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4821_, lean_object* v_x_4822_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = lean_apply_1(v_f_4821_, v_x_4822_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4824_, lean_object* v_f_4825_, lean_object* v_i_4826_, lean_object* v_acc_4827_){
_start:
{
lean_object* v___x_4828_; uint8_t v___x_4829_; 
v___x_4828_ = lean_array_get_size(v_a_4824_);
v___x_4829_ = lean_nat_dec_lt(v_i_4826_, v___x_4828_);
if (v___x_4829_ == 0)
{
lean_dec(v_i_4826_);
lean_dec_ref(v_f_4825_);
return v_acc_4827_;
}
else
{
lean_object* v_stx_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v_stx_4830_ = lean_array_fget_borrowed(v_a_4824_, v_i_4826_);
v___x_4831_ = lean_unsigned_to_nat(2u);
v___x_4832_ = lean_nat_mod(v_i_4826_, v___x_4831_);
v___x_4833_ = lean_unsigned_to_nat(0u);
v___x_4834_ = lean_nat_dec_eq(v___x_4832_, v___x_4833_);
lean_dec(v___x_4832_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4835_ = lean_unsigned_to_nat(1u);
v___x_4836_ = lean_nat_add(v_i_4826_, v___x_4835_);
lean_dec(v_i_4826_);
lean_inc(v_stx_4830_);
v___x_4837_ = lean_array_push(v_acc_4827_, v_stx_4830_);
v_i_4826_ = v___x_4836_;
v_acc_4827_ = v___x_4837_;
goto _start;
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_inc_ref(v_f_4825_);
lean_inc(v_stx_4830_);
v___x_4839_ = lean_apply_1(v_f_4825_, v_stx_4830_);
v___x_4840_ = lean_unsigned_to_nat(1u);
v___x_4841_ = lean_nat_add(v_i_4826_, v___x_4840_);
lean_dec(v_i_4826_);
v___x_4842_ = lean_array_push(v_acc_4827_, v___x_4839_);
v_i_4826_ = v___x_4841_;
v_acc_4827_ = v___x_4842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4844_, lean_object* v_f_4845_, lean_object* v_i_4846_, lean_object* v_acc_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4844_, v_f_4845_, v_i_4846_, v_acc_4847_);
lean_dec_ref(v_a_4844_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4849_, lean_object* v_f_4850_){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = lean_unsigned_to_nat(0u);
v___x_4852_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4853_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4849_, v_f_4850_, v___x_4851_, v___x_4852_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4854_, lean_object* v_f_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4854_, v_f_4855_);
lean_dec_ref(v_a_4854_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4857_, lean_object* v_f_4858_){
_start:
{
lean_object* v___f_4859_; lean_object* v___x_4860_; 
v___f_4859_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4859_, 0, v_f_4858_);
v___x_4860_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4857_, v___f_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4861_, lean_object* v_f_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Array_mapSepElems(v_a_4861_, v_f_4862_);
lean_dec_ref(v_a_4861_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4864_, size_t v_i_4865_, size_t v_stop_4866_, lean_object* v_b_4867_){
_start:
{
lean_object* v___y_4869_; uint8_t v___x_4873_; 
v___x_4873_ = lean_usize_dec_eq(v_i_4865_, v_stop_4866_);
if (v___x_4873_ == 0)
{
lean_object* v_fst_4874_; uint8_t v___x_4875_; 
v_fst_4874_ = lean_ctor_get(v_b_4867_, 0);
v___x_4875_ = lean_unbox(v_fst_4874_);
if (v___x_4875_ == 0)
{
lean_object* v_snd_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4885_; 
v_snd_4876_ = lean_ctor_get(v_b_4867_, 1);
v_isSharedCheck_4885_ = !lean_is_exclusive(v_b_4867_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; 
v_unused_4886_ = lean_ctor_get(v_b_4867_, 0);
lean_dec(v_unused_4886_);
v___x_4878_ = v_b_4867_;
v_isShared_4879_ = v_isSharedCheck_4885_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_snd_4876_);
lean_dec(v_b_4867_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4885_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
uint8_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4880_ = 1;
v___x_4881_ = lean_box(v___x_4880_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4881_);
v___x_4883_ = v___x_4878_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_snd_4876_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
v___y_4869_ = v___x_4883_;
goto v___jp_4868_;
}
}
}
else
{
lean_object* v_snd_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4897_; 
v_snd_4887_ = lean_ctor_get(v_b_4867_, 1);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_b_4867_);
if (v_isSharedCheck_4897_ == 0)
{
lean_object* v_unused_4898_; 
v_unused_4898_ = lean_ctor_get(v_b_4867_, 0);
lean_dec(v_unused_4898_);
v___x_4889_ = v_b_4867_;
v_isShared_4890_ = v_isSharedCheck_4897_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_snd_4887_);
lean_dec(v_b_4867_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4897_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4891_ = lean_array_uget_borrowed(v_as_4864_, v_i_4865_);
lean_inc(v___x_4891_);
v___x_4892_ = lean_array_push(v_snd_4887_, v___x_4891_);
v___x_4893_ = lean_box(v___x_4873_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 1, v___x_4892_);
lean_ctor_set(v___x_4889_, 0, v___x_4893_);
v___x_4895_ = v___x_4889_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v___x_4892_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
v___y_4869_ = v___x_4895_;
goto v___jp_4868_;
}
}
}
}
else
{
return v_b_4867_;
}
v___jp_4868_:
{
size_t v___x_4870_; size_t v___x_4871_; 
v___x_4870_ = ((size_t)1ULL);
v___x_4871_ = lean_usize_add(v_i_4865_, v___x_4870_);
v_i_4865_ = v___x_4871_;
v_b_4867_ = v___y_4869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4899_, lean_object* v_i_4900_, lean_object* v_stop_4901_, lean_object* v_b_4902_){
_start:
{
size_t v_i_boxed_4903_; size_t v_stop_boxed_4904_; lean_object* v_res_4905_; 
v_i_boxed_4903_ = lean_unbox_usize(v_i_4900_);
lean_dec(v_i_4900_);
v_stop_boxed_4904_ = lean_unbox_usize(v_stop_4901_);
lean_dec(v_stop_4901_);
v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4899_, v_i_boxed_4903_, v_stop_boxed_4904_, v_b_4902_);
lean_dec_ref(v_as_4899_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4906_){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; 
v___x_4907_ = lean_unsigned_to_nat(0u);
v___x_4908_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4909_ = lean_array_get_size(v_sa_4906_);
v___x_4910_ = lean_nat_dec_lt(v___x_4907_, v___x_4909_);
if (v___x_4910_ == 0)
{
return v___x_4908_;
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; size_t v___x_4913_; size_t v___x_4914_; lean_object* v___x_4915_; lean_object* v_snd_4916_; 
v___x_4911_ = lean_box(v___x_4910_);
v___x_4912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
lean_ctor_set(v___x_4912_, 1, v___x_4908_);
v___x_4913_ = ((size_t)0ULL);
v___x_4914_ = lean_usize_of_nat(v___x_4909_);
v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4906_, v___x_4913_, v___x_4914_, v___x_4912_);
v_snd_4916_ = lean_ctor_get(v___x_4915_, 1);
lean_inc(v_snd_4916_);
lean_dec_ref(v___x_4915_);
return v_snd_4916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4917_);
lean_dec_ref(v_sa_4917_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4919_, lean_object* v_sa_4920_){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4920_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4922_, lean_object* v_sa_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Lean_Syntax_SepArray_getElems(v_sep_4922_, v_sa_4923_);
lean_dec_ref(v_sa_4923_);
lean_dec_ref(v_sep_4922_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4925_){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; uint8_t v___x_4929_; 
v___x_4926_ = lean_unsigned_to_nat(0u);
v___x_4927_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4928_ = lean_array_get_size(v_sa_4925_);
v___x_4929_ = lean_nat_dec_lt(v___x_4926_, v___x_4928_);
if (v___x_4929_ == 0)
{
return v___x_4927_;
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; size_t v___x_4932_; size_t v___x_4933_; lean_object* v___x_4934_; lean_object* v_snd_4935_; 
v___x_4930_ = lean_box(v___x_4929_);
v___x_4931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
lean_ctor_set(v___x_4931_, 1, v___x_4927_);
v___x_4932_ = ((size_t)0ULL);
v___x_4933_ = lean_usize_of_nat(v___x_4928_);
v___x_4934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4925_, v___x_4932_, v___x_4933_, v___x_4931_);
v_snd_4935_ = lean_ctor_get(v___x_4934_, 1);
lean_inc(v_snd_4935_);
lean_dec_ref(v___x_4934_);
return v_snd_4935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4936_);
lean_dec_ref(v_sa_4936_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4938_, lean_object* v_sep_4939_, lean_object* v_sa_4940_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4942_, lean_object* v_sep_4943_, lean_object* v_sa_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Syntax_TSepArray_getElems(v_k_4942_, v_sep_4943_, v_sa_4944_);
lean_dec_ref(v_sa_4944_);
lean_dec_ref(v_sep_4943_);
lean_dec(v_k_4942_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4946_, lean_object* v_sa_4947_, lean_object* v_e_4948_){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4949_ = lean_array_get_size(v_sa_4947_);
v___x_4950_ = lean_unsigned_to_nat(0u);
v___x_4951_ = lean_nat_dec_eq(v___x_4949_, v___x_4950_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4952_ = l_Lean_mkAtom(v_sep_4946_);
v___x_4953_ = lean_array_push(v_sa_4947_, v___x_4952_);
v___x_4954_ = lean_array_push(v___x_4953_, v_e_4948_);
return v___x_4954_;
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
lean_dec_ref(v_sa_4947_);
lean_dec_ref(v_sep_4946_);
v___x_4955_ = lean_unsigned_to_nat(1u);
v___x_4956_ = lean_mk_empty_array_with_capacity(v___x_4955_);
v___x_4957_ = lean_array_push(v___x_4956_, v_e_4948_);
return v___x_4957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4958_, lean_object* v_sep_4959_, lean_object* v_sa_4960_, lean_object* v_e_4961_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4959_, v_sa_4960_, v_e_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4963_, lean_object* v_sep_4964_, lean_object* v_sa_4965_, lean_object* v_e_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Syntax_TSepArray_push(v_k_4963_, v_sep_4964_, v_sa_4965_, v_e_4966_);
lean_dec(v_k_4963_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4969_; 
v___x_4969_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4971_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4973_){
_start:
{
lean_object* v___x_4974_; 
v___x_4974_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4975_);
lean_dec_ref(v_sep_4975_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4978_; 
v___x_4978_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4980_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4982_, lean_object* v_k_4983_){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4985_, lean_object* v_k_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4985_, v_k_4986_);
lean_dec_ref(v_k_4986_);
lean_dec(v_sep_4985_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4988_){
_start:
{
lean_inc_ref(v_v_4988_);
return v_v_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4989_);
lean_dec_ref(v_v_4989_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4993_; 
v___f_4993_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4996_, lean_object* v_sep_4997_){
_start:
{
lean_object* v___f_4998_; 
v___f_4998_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4999_, lean_object* v_sep_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4999_, v_sep_5000_);
lean_dec_ref(v_sep_5000_);
lean_dec(v_k_4999_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_5002_, lean_object* v_sep_5003_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_5004_, 0, v_k_5002_);
lean_closure_set(v___x_5004_, 1, v_sep_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_5005_, lean_object* v_x_5006_){
_start:
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_apply_1(v_inst_5005_, v_x_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v___x_5010_; size_t v_sz_5011_; size_t v___x_5012_; lean_object* v___x_5013_; 
v___x_5010_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5011_ = lean_array_size(v_a_5009_);
v___x_5012_ = ((size_t)0ULL);
v___x_5013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5010_, v___f_5008_, v_sz_5011_, v___x_5012_, v_a_5009_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5014_){
_start:
{
lean_object* v___f_5015_; lean_object* v___f_5016_; 
v___f_5015_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5015_, 0, v_inst_5014_);
v___f_5016_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5016_, 0, v___f_5015_);
return v___f_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5017_, lean_object* v_k_x27_5018_, lean_object* v_inst_5019_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5021_, lean_object* v_k_x27_5022_, lean_object* v_inst_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5021_, v_k_x27_5022_, v_inst_5023_);
lean_dec(v_k_x27_5022_);
lean_dec(v_k_5021_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_5025_){
_start:
{
lean_inc_ref(v_a_5025_);
return v_a_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_5026_);
lean_dec_ref(v_a_5026_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_5030_; 
v___f_5030_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5033_){
_start:
{
lean_object* v___f_5034_; 
v___f_5034_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5035_);
lean_dec(v_k_5035_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5043_){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5044_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5045_ = lean_box(2);
v___x_5046_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5047_ = lean_unsigned_to_nat(2u);
v___x_5048_ = lean_mk_empty_array_with_capacity(v___x_5047_);
v___x_5049_ = lean_array_push(v___x_5048_, v_id_5043_);
v___x_5050_ = lean_array_push(v___x_5049_, v___x_5046_);
v___x_5051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5045_);
lean_ctor_set(v___x_5051_, 1, v___x_5044_);
lean_ctor_set(v___x_5051_, 2, v___x_5050_);
return v___x_5051_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = 123;
v___x_5056_ = lean_box_uint32(v___x_5055_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5057_, lean_object* v_i_5058_){
_start:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Lean_Syntax_decodeQuotedChar(v_s_5057_, v_i_5058_);
if (lean_obj_tag(v___x_5059_) == 0)
{
uint32_t v_c_5060_; uint32_t v___x_5061_; uint8_t v___x_5062_; 
v_c_5060_ = lean_string_utf8_get(v_s_5057_, v_i_5058_);
v___x_5061_ = 123;
v___x_5062_ = lean_uint32_dec_eq(v_c_5060_, v___x_5061_);
if (v___x_5062_ == 0)
{
return v___x_5059_;
}
else
{
lean_object* v_i_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v_i_5063_ = lean_string_utf8_next(v_s_5057_, v_i_5058_);
v___x_5064_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
lean_ctor_set(v___x_5065_, 1, v_i_5063_);
v___x_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
return v___x_5066_;
}
}
else
{
return v___x_5059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5067_, lean_object* v_i_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5067_, v_i_5068_);
lean_dec(v_i_5068_);
lean_dec_ref(v_s_5067_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5070_, lean_object* v_i_5071_, lean_object* v_acc_5072_){
_start:
{
uint32_t v_c_5073_; uint32_t v___x_5074_; uint8_t v___x_5075_; 
v_c_5073_ = lean_string_utf8_get(v_s_5070_, v_i_5071_);
v___x_5074_ = 34;
v___x_5075_ = lean_uint32_dec_eq(v_c_5073_, v___x_5074_);
if (v___x_5075_ == 0)
{
uint32_t v___x_5076_; uint8_t v___x_5077_; 
v___x_5076_ = 123;
v___x_5077_ = lean_uint32_dec_eq(v_c_5073_, v___x_5076_);
if (v___x_5077_ == 0)
{
lean_object* v_i_5078_; uint8_t v___x_5079_; 
v_i_5078_ = lean_string_utf8_next(v_s_5070_, v_i_5071_);
lean_dec(v_i_5071_);
v___x_5079_ = lean_string_utf8_at_end(v_s_5070_, v_i_5078_);
if (v___x_5079_ == 0)
{
uint32_t v___x_5080_; uint8_t v___x_5081_; 
v___x_5080_ = 92;
v___x_5081_ = lean_uint32_dec_eq(v_c_5073_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; 
v___x_5082_ = lean_string_push(v_acc_5072_, v_c_5073_);
v_i_5071_ = v_i_5078_;
v_acc_5072_ = v___x_5082_;
goto _start;
}
else
{
lean_object* v___x_5084_; 
v___x_5084_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5070_, v_i_5078_);
if (lean_obj_tag(v___x_5084_) == 1)
{
lean_object* v_val_5085_; lean_object* v_fst_5086_; lean_object* v_snd_5087_; uint32_t v___x_5088_; lean_object* v___x_5089_; 
lean_dec(v_i_5078_);
v_val_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_val_5085_);
lean_dec_ref_known(v___x_5084_, 1);
v_fst_5086_ = lean_ctor_get(v_val_5085_, 0);
lean_inc(v_fst_5086_);
v_snd_5087_ = lean_ctor_get(v_val_5085_, 1);
lean_inc(v_snd_5087_);
lean_dec(v_val_5085_);
v___x_5088_ = lean_unbox_uint32(v_fst_5086_);
lean_dec(v_fst_5086_);
v___x_5089_ = lean_string_push(v_acc_5072_, v___x_5088_);
v_i_5071_ = v_snd_5087_;
v_acc_5072_ = v___x_5089_;
goto _start;
}
else
{
lean_object* v___x_5091_; 
lean_dec(v___x_5084_);
lean_inc_ref(v_s_5070_);
v___x_5091_ = l_Lean_Syntax_decodeStringGap(v_s_5070_, v_i_5078_);
lean_dec(v_i_5078_);
if (lean_obj_tag(v___x_5091_) == 1)
{
lean_object* v_val_5092_; 
v_val_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_val_5092_);
lean_dec_ref_known(v___x_5091_, 1);
v_i_5071_ = v_val_5092_;
goto _start;
}
else
{
lean_object* v___x_5094_; 
lean_dec(v___x_5091_);
lean_dec_ref(v_acc_5072_);
lean_dec_ref(v_s_5070_);
v___x_5094_ = lean_box(0);
return v___x_5094_;
}
}
}
}
else
{
lean_object* v___x_5095_; 
lean_dec(v_i_5078_);
lean_dec_ref(v_acc_5072_);
lean_dec_ref(v_s_5070_);
v___x_5095_ = lean_box(0);
return v___x_5095_;
}
}
else
{
lean_object* v___x_5096_; 
lean_dec(v_i_5071_);
lean_dec_ref(v_s_5070_);
v___x_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5096_, 0, v_acc_5072_);
return v___x_5096_;
}
}
else
{
lean_object* v___x_5097_; 
lean_dec(v_i_5071_);
lean_dec_ref(v_s_5070_);
v___x_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5097_, 0, v_acc_5072_);
return v___x_5097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5098_){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5099_ = lean_unsigned_to_nat(1u);
v___x_5100_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5101_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5098_, v___x_5099_, v___x_5100_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5105_){
_start:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5107_ = l_Lean_Syntax_isLit_x3f(v___x_5106_, v_stx_5105_);
if (lean_obj_tag(v___x_5107_) == 0)
{
return v___x_5107_;
}
else
{
lean_object* v_val_5108_; lean_object* v___x_5109_; 
v_val_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_val_5108_);
lean_dec_ref_known(v___x_5107_, 1);
v___x_5109_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5108_);
return v___x_5109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5110_);
lean_dec(v_stx_5110_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5112_){
_start:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; 
v___x_5113_ = l_Lean_Syntax_getArgs(v_stx_5112_);
v___x_5114_ = lean_unsigned_to_nat(0u);
v___x_5115_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5116_ = lean_array_get_size(v___x_5113_);
v___x_5117_ = lean_nat_dec_lt(v___x_5114_, v___x_5116_);
if (v___x_5117_ == 0)
{
lean_dec_ref(v___x_5113_);
return v___x_5115_;
}
else
{
lean_object* v___x_5118_; lean_object* v___x_5119_; size_t v___x_5120_; size_t v___x_5121_; lean_object* v___x_5122_; lean_object* v_snd_5123_; 
v___x_5118_ = lean_box(v___x_5117_);
v___x_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5118_);
lean_ctor_set(v___x_5119_, 1, v___x_5115_);
v___x_5120_ = ((size_t)0ULL);
v___x_5121_ = lean_usize_of_nat(v___x_5116_);
v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5113_, v___x_5120_, v___x_5121_, v___x_5119_);
lean_dec_ref(v___x_5113_);
v_snd_5123_ = lean_ctor_get(v___x_5122_, 1);
lean_inc(v_snd_5123_);
lean_dec_ref(v___x_5122_);
return v_snd_5123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_Syntax_getSepArgs(v_stx_5124_);
lean_dec(v_stx_5124_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5126_, lean_object* v_mkElem_5127_, lean_object* v_mkLit_5128_, lean_object* v_as_5129_, size_t v_sz_5130_, size_t v_i_5131_, lean_object* v_b_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_){
_start:
{
lean_object* v_a_5136_; lean_object* v_a_5137_; lean_object* v_elem_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; uint8_t v___x_5149_; 
v___x_5149_ = lean_usize_dec_lt(v_i_5131_, v_sz_5130_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5150_; 
lean_dec_ref(v_mkLit_5128_);
lean_dec_ref(v_mkElem_5127_);
lean_dec_ref(v_mkAppend_5126_);
v___x_5150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5150_, 0, v_b_5132_);
lean_ctor_set(v___x_5150_, 1, v___y_5134_);
return v___x_5150_;
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5152_; 
v_a_5151_ = lean_array_uget_borrowed(v_as_5129_, v_i_5131_);
v___x_5152_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5151_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_object* v_methods_5153_; lean_object* v_quotContext_5154_; lean_object* v_currMacroScope_5155_; lean_object* v_currRecDepth_5156_; lean_object* v_maxRecDepth_5157_; lean_object* v_ref_5158_; lean_object* v_ref_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
v_methods_5153_ = lean_ctor_get(v___y_5133_, 0);
v_quotContext_5154_ = lean_ctor_get(v___y_5133_, 1);
v_currMacroScope_5155_ = lean_ctor_get(v___y_5133_, 2);
v_currRecDepth_5156_ = lean_ctor_get(v___y_5133_, 3);
v_maxRecDepth_5157_ = lean_ctor_get(v___y_5133_, 4);
v_ref_5158_ = lean_ctor_get(v___y_5133_, 5);
v_ref_5159_ = l_Lean_replaceRef(v_a_5151_, v_ref_5158_);
lean_inc(v_maxRecDepth_5157_);
lean_inc(v_currRecDepth_5156_);
lean_inc(v_currMacroScope_5155_);
lean_inc(v_quotContext_5154_);
lean_inc(v_methods_5153_);
v___x_5160_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5160_, 0, v_methods_5153_);
lean_ctor_set(v___x_5160_, 1, v_quotContext_5154_);
lean_ctor_set(v___x_5160_, 2, v_currMacroScope_5155_);
lean_ctor_set(v___x_5160_, 3, v_currRecDepth_5156_);
lean_ctor_set(v___x_5160_, 4, v_maxRecDepth_5157_);
lean_ctor_set(v___x_5160_, 5, v_ref_5159_);
lean_inc_ref(v_mkElem_5127_);
lean_inc(v_a_5151_);
v___x_5161_ = lean_apply_3(v_mkElem_5127_, v_a_5151_, v___x_5160_, v___y_5134_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v_a_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
v_a_5163_ = lean_ctor_get(v___x_5161_, 1);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5161_, 2);
v_elem_5142_ = v_a_5162_;
v___y_5143_ = v___y_5133_;
v___y_5144_ = v_a_5163_;
goto v___jp_5141_;
}
else
{
lean_dec(v_b_5132_);
lean_dec_ref(v_mkLit_5128_);
lean_dec_ref(v_mkElem_5127_);
lean_dec_ref(v_mkAppend_5126_);
return v___x_5161_;
}
}
else
{
lean_object* v_val_5164_; uint8_t v___x_5165_; 
v_val_5164_ = lean_ctor_get(v___x_5152_, 0);
lean_inc_n(v_val_5164_, 2);
lean_dec_ref_known(v___x_5152_, 1);
v___x_5165_ = lean_string_isempty(v_val_5164_);
if (v___x_5165_ == 0)
{
lean_object* v_methods_5166_; lean_object* v_quotContext_5167_; lean_object* v_currMacroScope_5168_; lean_object* v_currRecDepth_5169_; lean_object* v_maxRecDepth_5170_; lean_object* v_ref_5171_; lean_object* v_ref_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v_methods_5166_ = lean_ctor_get(v___y_5133_, 0);
v_quotContext_5167_ = lean_ctor_get(v___y_5133_, 1);
v_currMacroScope_5168_ = lean_ctor_get(v___y_5133_, 2);
v_currRecDepth_5169_ = lean_ctor_get(v___y_5133_, 3);
v_maxRecDepth_5170_ = lean_ctor_get(v___y_5133_, 4);
v_ref_5171_ = lean_ctor_get(v___y_5133_, 5);
v_ref_5172_ = l_Lean_replaceRef(v_a_5151_, v_ref_5171_);
lean_inc(v_maxRecDepth_5170_);
lean_inc(v_currRecDepth_5169_);
lean_inc(v_currMacroScope_5168_);
lean_inc(v_quotContext_5167_);
lean_inc(v_methods_5166_);
v___x_5173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5173_, 0, v_methods_5166_);
lean_ctor_set(v___x_5173_, 1, v_quotContext_5167_);
lean_ctor_set(v___x_5173_, 2, v_currMacroScope_5168_);
lean_ctor_set(v___x_5173_, 3, v_currRecDepth_5169_);
lean_ctor_set(v___x_5173_, 4, v_maxRecDepth_5170_);
lean_ctor_set(v___x_5173_, 5, v_ref_5172_);
lean_inc_ref(v_mkLit_5128_);
v___x_5174_ = lean_apply_3(v_mkLit_5128_, v_val_5164_, v___x_5173_, v___y_5134_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v_a_5176_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5175_);
v_a_5176_ = lean_ctor_get(v___x_5174_, 1);
lean_inc(v_a_5176_);
lean_dec_ref_known(v___x_5174_, 2);
v_elem_5142_ = v_a_5175_;
v___y_5143_ = v___y_5133_;
v___y_5144_ = v_a_5176_;
goto v___jp_5141_;
}
else
{
lean_dec(v_b_5132_);
lean_dec_ref(v_mkLit_5128_);
lean_dec_ref(v_mkElem_5127_);
lean_dec_ref(v_mkAppend_5126_);
return v___x_5174_;
}
}
else
{
lean_dec(v_val_5164_);
v_a_5136_ = v_b_5132_;
v_a_5137_ = v___y_5134_;
goto v___jp_5135_;
}
}
}
v___jp_5135_:
{
size_t v___x_5138_; size_t v___x_5139_; 
v___x_5138_ = ((size_t)1ULL);
v___x_5139_ = lean_usize_add(v_i_5131_, v___x_5138_);
v_i_5131_ = v___x_5139_;
v_b_5132_ = v_a_5136_;
v___y_5134_ = v_a_5137_;
goto _start;
}
v___jp_5141_:
{
uint8_t v___x_5145_; 
v___x_5145_ = l_Lean_Syntax_isMissing(v_b_5132_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
lean_inc_ref(v_mkAppend_5126_);
lean_inc_ref(v___y_5143_);
v___x_5146_ = lean_apply_4(v_mkAppend_5126_, v_b_5132_, v_elem_5142_, v___y_5143_, v___y_5144_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v_a_5148_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
v_a_5148_ = lean_ctor_get(v___x_5146_, 1);
lean_inc(v_a_5148_);
lean_dec_ref_known(v___x_5146_, 2);
v_a_5136_ = v_a_5147_;
v_a_5137_ = v_a_5148_;
goto v___jp_5135_;
}
else
{
lean_dec_ref(v_mkLit_5128_);
lean_dec_ref(v_mkElem_5127_);
lean_dec_ref(v_mkAppend_5126_);
return v___x_5146_;
}
}
else
{
lean_dec(v_b_5132_);
v_a_5136_ = v_elem_5142_;
v_a_5137_ = v___y_5144_;
goto v___jp_5135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5177_, lean_object* v_mkElem_5178_, lean_object* v_mkLit_5179_, lean_object* v_as_5180_, lean_object* v_sz_5181_, lean_object* v_i_5182_, lean_object* v_b_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
size_t v_sz_boxed_5186_; size_t v_i_boxed_5187_; lean_object* v_res_5188_; 
v_sz_boxed_5186_ = lean_unbox_usize(v_sz_5181_);
lean_dec(v_sz_5181_);
v_i_boxed_5187_ = lean_unbox_usize(v_i_5182_);
lean_dec(v_i_5182_);
v_res_5188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5177_, v_mkElem_5178_, v_mkLit_5179_, v_as_5180_, v_sz_boxed_5186_, v_i_boxed_5187_, v_b_5183_, v___y_5184_, v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec_ref(v_as_5180_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5189_, lean_object* v_mkAppend_5190_, lean_object* v_mkElem_5191_, lean_object* v_mkLit_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_){
_start:
{
lean_object* v_result_5195_; size_t v_sz_5196_; size_t v___x_5197_; lean_object* v___x_5198_; 
v_result_5195_ = lean_box(0);
v_sz_5196_ = lean_array_size(v_chunks_5189_);
v___x_5197_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5192_);
v___x_5198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5190_, v_mkElem_5191_, v_mkLit_5192_, v_chunks_5189_, v_sz_5196_, v___x_5197_, v_result_5195_, v_a_5193_, v_a_5194_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v_a_5200_; uint8_t v___x_5201_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5199_);
v_a_5200_ = lean_ctor_get(v___x_5198_, 1);
lean_inc(v_a_5200_);
v___x_5201_ = l_Lean_Syntax_isMissing(v_a_5199_);
lean_dec(v_a_5199_);
if (v___x_5201_ == 0)
{
lean_dec(v_a_5200_);
lean_dec_ref(v_mkLit_5192_);
return v___x_5198_;
}
else
{
lean_object* v___x_5202_; lean_object* v___x_5203_; 
lean_dec_ref_known(v___x_5198_, 2);
v___x_5202_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5193_);
v___x_5203_ = lean_apply_3(v_mkLit_5192_, v___x_5202_, v_a_5193_, v_a_5200_);
return v___x_5203_;
}
}
else
{
lean_dec_ref(v_mkLit_5192_);
return v___x_5198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5204_, lean_object* v_mkAppend_5205_, lean_object* v_mkElem_5206_, lean_object* v_mkLit_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5204_, v_mkAppend_5205_, v_mkElem_5206_, v_mkLit_5207_, v_a_5208_, v_a_5209_);
lean_dec_ref(v_a_5208_);
lean_dec_ref(v_chunks_5204_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5215_, lean_object* v_b_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_ref_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v_ref_5219_ = lean_ctor_get(v___y_5217_, 5);
v___x_5220_ = 0;
v___x_5221_ = l_Lean_SourceInfo_fromRef(v_ref_5219_, v___x_5220_);
v___x_5222_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5223_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5221_);
v___x_5224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5221_);
lean_ctor_set(v___x_5224_, 1, v___x_5223_);
v___x_5225_ = l_Lean_Syntax_node3(v___x_5221_, v___x_5222_, v_a_5215_, v___x_5224_, v_b_5216_);
v___x_5226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5225_);
lean_ctor_set(v___x_5226_, 1, v___y_5218_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5227_, lean_object* v_b_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5227_, v_b_5228_, v___y_5229_, v___y_5230_);
lean_dec_ref(v___y_5229_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5232_, lean_object* v_a_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v_ref_5236_; uint8_t v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
v_ref_5236_ = lean_ctor_get(v___y_5234_, 5);
v___x_5237_ = 0;
v___x_5238_ = l_Lean_SourceInfo_fromRef(v_ref_5236_, v___x_5237_);
v___x_5239_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5240_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5238_);
v___x_5241_ = l_Lean_Syntax_node1(v___x_5238_, v___x_5240_, v_a_5233_);
v___x_5242_ = l_Lean_Syntax_node2(v___x_5238_, v___x_5239_, v_ofInterpFn_5232_, v___x_5241_);
v___x_5243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5242_);
lean_ctor_set(v___x_5243_, 1, v___y_5235_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5244_, lean_object* v_a_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v_res_5248_; 
v_res_5248_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5244_, v_a_5245_, v___y_5246_, v___y_5247_);
lean_dec_ref(v___y_5246_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5249_, lean_object* v_s_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_){
_start:
{
lean_object* v_ref_5253_; uint8_t v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v_ref_5253_ = lean_ctor_get(v___y_5251_, 5);
v___x_5254_ = 0;
v___x_5255_ = l_Lean_SourceInfo_fromRef(v_ref_5253_, v___x_5254_);
v___x_5256_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5257_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5258_ = lean_box(2);
v___x_5259_ = l_Lean_Syntax_mkStrLit(v_s_5250_, v___x_5258_);
lean_inc(v___x_5255_);
v___x_5260_ = l_Lean_Syntax_node1(v___x_5255_, v___x_5257_, v___x_5259_);
v___x_5261_ = l_Lean_Syntax_node2(v___x_5255_, v___x_5256_, v_ofLitFn_5249_, v___x_5260_);
v___x_5262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5261_);
lean_ctor_set(v___x_5262_, 1, v___y_5252_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5263_, lean_object* v_s_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5263_, v_s_5264_, v___y_5265_, v___y_5266_);
lean_dec_ref(v___y_5265_);
return v_res_5267_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5285_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5286_ = l_String_toRawSubstring_x27(v___x_5285_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5307_, lean_object* v_type_5308_, lean_object* v_ofInterpFn_5309_, lean_object* v_ofLitFn_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_){
_start:
{
lean_object* v___f_5313_; lean_object* v___f_5314_; lean_object* v___f_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___f_5313_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5314_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5314_, 0, v_ofInterpFn_5309_);
v___f_5315_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5315_, 0, v_ofLitFn_5310_);
v___x_5316_ = l_Lean_Syntax_getArgs(v_interpStr_5307_);
v___x_5317_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5316_, v___f_5313_, v___f_5314_, v___f_5315_, v_a_5311_, v_a_5312_);
lean_dec_ref(v___x_5316_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_a_5318_; lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5350_; 
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
v_a_5319_ = lean_ctor_get(v___x_5317_, 1);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5321_ = v___x_5317_;
v_isShared_5322_ = v_isSharedCheck_5350_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_inc(v_a_5318_);
lean_dec(v___x_5317_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5350_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v_quotContext_5323_; lean_object* v_currMacroScope_5324_; lean_object* v_ref_5325_; uint8_t v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
v_quotContext_5323_ = lean_ctor_get(v_a_5311_, 1);
v_currMacroScope_5324_ = lean_ctor_get(v_a_5311_, 2);
v_ref_5325_ = lean_ctor_get(v_a_5311_, 5);
v___x_5326_ = 0;
v___x_5327_ = l_Lean_SourceInfo_fromRef(v_ref_5325_, v___x_5326_);
v___x_5328_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5329_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5330_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5327_, 7);
v___x_5331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5327_);
lean_ctor_set(v___x_5331_, 1, v___x_5330_);
v___x_5332_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5333_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5334_ = lean_box(0);
lean_inc(v_currMacroScope_5324_);
lean_inc(v_quotContext_5323_);
v___x_5335_ = l_Lean_addMacroScope(v_quotContext_5323_, v___x_5334_, v_currMacroScope_5324_);
v___x_5336_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5327_);
lean_ctor_set(v___x_5337_, 1, v___x_5333_);
lean_ctor_set(v___x_5337_, 2, v___x_5335_);
lean_ctor_set(v___x_5337_, 3, v___x_5336_);
v___x_5338_ = l_Lean_Syntax_node1(v___x_5327_, v___x_5332_, v___x_5337_);
v___x_5339_ = l_Lean_Syntax_node2(v___x_5327_, v___x_5329_, v___x_5331_, v___x_5338_);
v___x_5340_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5327_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5343_ = l_Lean_Syntax_node1(v___x_5327_, v___x_5342_, v_type_5308_);
v___x_5344_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5327_);
lean_ctor_set(v___x_5345_, 1, v___x_5344_);
v___x_5346_ = l_Lean_Syntax_node5(v___x_5327_, v___x_5328_, v___x_5339_, v_a_5318_, v___x_5341_, v___x_5343_, v___x_5345_);
if (v_isShared_5322_ == 0)
{
lean_ctor_set(v___x_5321_, 0, v___x_5346_);
v___x_5348_ = v___x_5321_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5346_);
lean_ctor_set(v_reuseFailAlloc_5349_, 1, v_a_5319_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
else
{
lean_object* v_a_5351_; lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec(v_type_5308_);
v_a_5351_ = lean_ctor_get(v___x_5317_, 0);
v_a_5352_ = lean_ctor_get(v___x_5317_, 1);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5317_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_inc(v_a_5351_);
lean_dec(v___x_5317_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5351_);
lean_ctor_set(v_reuseFailAlloc_5358_, 1, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5360_, lean_object* v_type_5361_, lean_object* v_ofInterpFn_5362_, lean_object* v_ofLitFn_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5360_, v_type_5361_, v_ofInterpFn_5362_, v_ofLitFn_5363_, v_a_5364_, v_a_5365_);
lean_dec_ref(v_a_5364_);
lean_dec(v_interpStr_5360_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5367_){
_start:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = lean_unsigned_to_nat(1u);
v___x_5369_ = l_Lean_Syntax_getArg(v_stx_5367_, v___x_5368_);
if (lean_obj_tag(v___x_5369_) == 1)
{
lean_object* v_kind_5370_; 
v_kind_5370_ = lean_ctor_get(v___x_5369_, 1);
lean_inc(v_kind_5370_);
if (lean_obj_tag(v_kind_5370_) == 1)
{
lean_object* v_pre_5371_; 
v_pre_5371_ = lean_ctor_get(v_kind_5370_, 0);
lean_inc(v_pre_5371_);
if (lean_obj_tag(v_pre_5371_) == 1)
{
lean_object* v_pre_5372_; 
v_pre_5372_ = lean_ctor_get(v_pre_5371_, 0);
lean_inc(v_pre_5372_);
if (lean_obj_tag(v_pre_5372_) == 1)
{
lean_object* v_pre_5373_; 
v_pre_5373_ = lean_ctor_get(v_pre_5372_, 0);
lean_inc(v_pre_5373_);
if (lean_obj_tag(v_pre_5373_) == 1)
{
lean_object* v_pre_5374_; 
v_pre_5374_ = lean_ctor_get(v_pre_5373_, 0);
if (lean_obj_tag(v_pre_5374_) == 0)
{
lean_object* v_args_5375_; lean_object* v_str_5376_; lean_object* v_str_5377_; lean_object* v_str_5378_; lean_object* v_str_5379_; lean_object* v___x_5380_; uint8_t v___x_5381_; 
v_args_5375_ = lean_ctor_get(v___x_5369_, 2);
lean_inc_ref(v_args_5375_);
lean_dec_ref_known(v___x_5369_, 3);
v_str_5376_ = lean_ctor_get(v_kind_5370_, 1);
lean_inc_ref(v_str_5376_);
lean_dec_ref_known(v_kind_5370_, 2);
v_str_5377_ = lean_ctor_get(v_pre_5371_, 1);
lean_inc_ref(v_str_5377_);
lean_dec_ref_known(v_pre_5371_, 2);
v_str_5378_ = lean_ctor_get(v_pre_5372_, 1);
lean_inc_ref(v_str_5378_);
lean_dec_ref_known(v_pre_5372_, 2);
v_str_5379_ = lean_ctor_get(v_pre_5373_, 1);
lean_inc_ref(v_str_5379_);
lean_dec_ref_known(v_pre_5373_, 2);
v___x_5380_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5381_ = lean_string_dec_eq(v_str_5379_, v___x_5380_);
lean_dec_ref(v_str_5379_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
lean_dec_ref(v_str_5378_);
lean_dec_ref(v_str_5377_);
lean_dec_ref(v_str_5376_);
lean_dec_ref(v_args_5375_);
v___x_5382_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5382_;
}
else
{
lean_object* v___x_5383_; uint8_t v___x_5384_; 
v___x_5383_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5384_ = lean_string_dec_eq(v_str_5378_, v___x_5383_);
lean_dec_ref(v_str_5378_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; 
lean_dec_ref(v_str_5377_);
lean_dec_ref(v_str_5376_);
lean_dec_ref(v_args_5375_);
v___x_5385_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5385_;
}
else
{
lean_object* v___x_5386_; uint8_t v___x_5387_; 
v___x_5386_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5387_ = lean_string_dec_eq(v_str_5377_, v___x_5386_);
lean_dec_ref(v_str_5377_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; 
lean_dec_ref(v_str_5376_);
lean_dec_ref(v_args_5375_);
v___x_5388_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5388_;
}
else
{
lean_object* v___x_5389_; uint8_t v___x_5390_; 
v___x_5389_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5390_ = lean_string_dec_eq(v_str_5376_, v___x_5389_);
lean_dec_ref(v_str_5376_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; 
lean_dec_ref(v_args_5375_);
v___x_5391_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5391_;
}
else
{
lean_object* v___x_5392_; lean_object* v___x_5393_; uint8_t v___x_5394_; 
v___x_5392_ = lean_array_get_size(v_args_5375_);
v___x_5393_ = lean_unsigned_to_nat(2u);
v___x_5394_ = lean_nat_dec_eq(v___x_5392_, v___x_5393_);
if (v___x_5394_ == 0)
{
lean_object* v___x_5395_; 
lean_dec_ref(v_args_5375_);
v___x_5395_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5395_;
}
else
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5396_ = lean_unsigned_to_nat(0u);
v___x_5397_ = lean_array_fget(v_args_5375_, v___x_5396_);
lean_dec_ref(v_args_5375_);
if (lean_obj_tag(v___x_5397_) == 2)
{
lean_object* v_val_5398_; 
v_val_5398_ = lean_ctor_get(v___x_5397_, 1);
lean_inc_ref(v_val_5398_);
lean_dec_ref_known(v___x_5397_, 2);
return v_val_5398_;
}
else
{
lean_object* v___x_5399_; 
lean_dec(v___x_5397_);
v___x_5399_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5399_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5400_; 
lean_dec_ref_known(v_pre_5373_, 2);
lean_dec_ref_known(v_pre_5372_, 2);
lean_dec_ref_known(v_pre_5371_, 2);
lean_dec_ref_known(v_kind_5370_, 2);
lean_dec_ref_known(v___x_5369_, 3);
v___x_5400_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5400_;
}
}
else
{
lean_object* v___x_5401_; 
lean_dec_ref_known(v_pre_5372_, 2);
lean_dec(v_pre_5373_);
lean_dec_ref_known(v_pre_5371_, 2);
lean_dec_ref_known(v_kind_5370_, 2);
lean_dec_ref_known(v___x_5369_, 3);
v___x_5401_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5401_;
}
}
else
{
lean_object* v___x_5402_; 
lean_dec(v_pre_5372_);
lean_dec_ref_known(v_pre_5371_, 2);
lean_dec_ref_known(v_kind_5370_, 2);
lean_dec_ref_known(v___x_5369_, 3);
v___x_5402_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5402_;
}
}
else
{
lean_object* v___x_5403_; 
lean_dec(v_pre_5371_);
lean_dec_ref_known(v_kind_5370_, 2);
lean_dec_ref_known(v___x_5369_, 3);
v___x_5403_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5403_;
}
}
else
{
lean_object* v___x_5404_; 
lean_dec_ref_known(v___x_5369_, 3);
lean_dec(v_kind_5370_);
v___x_5404_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5404_;
}
}
else
{
lean_object* v___x_5405_; 
lean_dec(v___x_5369_);
v___x_5405_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l_Lean_TSyntax_getDocString(v_stx_5406_);
lean_dec(v_stx_5406_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5426_, lean_object* v_prec_5427_){
_start:
{
lean_object* v___y_5429_; lean_object* v___y_5436_; lean_object* v___y_5443_; lean_object* v___y_5450_; lean_object* v___y_5457_; lean_object* v___y_5464_; 
switch(v_x_5426_)
{
case 0:
{
lean_object* v___x_5470_; uint8_t v___x_5471_; 
v___x_5470_ = lean_unsigned_to_nat(1024u);
v___x_5471_ = lean_nat_dec_le(v___x_5470_, v_prec_5427_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5472_; 
v___x_5472_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5429_ = v___x_5472_;
goto v___jp_5428_;
}
else
{
lean_object* v___x_5473_; 
v___x_5473_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5429_ = v___x_5473_;
goto v___jp_5428_;
}
}
case 1:
{
lean_object* v___x_5474_; uint8_t v___x_5475_; 
v___x_5474_ = lean_unsigned_to_nat(1024u);
v___x_5475_ = lean_nat_dec_le(v___x_5474_, v_prec_5427_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5476_; 
v___x_5476_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5436_ = v___x_5476_;
goto v___jp_5435_;
}
else
{
lean_object* v___x_5477_; 
v___x_5477_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5436_ = v___x_5477_;
goto v___jp_5435_;
}
}
case 2:
{
lean_object* v___x_5478_; uint8_t v___x_5479_; 
v___x_5478_ = lean_unsigned_to_nat(1024u);
v___x_5479_ = lean_nat_dec_le(v___x_5478_, v_prec_5427_);
if (v___x_5479_ == 0)
{
lean_object* v___x_5480_; 
v___x_5480_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5443_ = v___x_5480_;
goto v___jp_5442_;
}
else
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5443_ = v___x_5481_;
goto v___jp_5442_;
}
}
case 3:
{
lean_object* v___x_5482_; uint8_t v___x_5483_; 
v___x_5482_ = lean_unsigned_to_nat(1024u);
v___x_5483_ = lean_nat_dec_le(v___x_5482_, v_prec_5427_);
if (v___x_5483_ == 0)
{
lean_object* v___x_5484_; 
v___x_5484_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5450_ = v___x_5484_;
goto v___jp_5449_;
}
else
{
lean_object* v___x_5485_; 
v___x_5485_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5450_ = v___x_5485_;
goto v___jp_5449_;
}
}
case 4:
{
lean_object* v___x_5486_; uint8_t v___x_5487_; 
v___x_5486_ = lean_unsigned_to_nat(1024u);
v___x_5487_ = lean_nat_dec_le(v___x_5486_, v_prec_5427_);
if (v___x_5487_ == 0)
{
lean_object* v___x_5488_; 
v___x_5488_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5457_ = v___x_5488_;
goto v___jp_5456_;
}
else
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5457_ = v___x_5489_;
goto v___jp_5456_;
}
}
default: 
{
lean_object* v___x_5490_; uint8_t v___x_5491_; 
v___x_5490_ = lean_unsigned_to_nat(1024u);
v___x_5491_ = lean_nat_dec_le(v___x_5490_, v_prec_5427_);
if (v___x_5491_ == 0)
{
lean_object* v___x_5492_; 
v___x_5492_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5464_ = v___x_5492_;
goto v___jp_5463_;
}
else
{
lean_object* v___x_5493_; 
v___x_5493_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5464_ = v___x_5493_;
goto v___jp_5463_;
}
}
}
v___jp_5428_:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5430_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5429_);
v___x_5431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5431_, 0, v___y_5429_);
lean_ctor_set(v___x_5431_, 1, v___x_5430_);
v___x_5432_ = 0;
v___x_5433_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5433_, 0, v___x_5431_);
lean_ctor_set_uint8(v___x_5433_, sizeof(void*)*1, v___x_5432_);
v___x_5434_ = l_Repr_addAppParen(v___x_5433_, v_prec_5427_);
return v___x_5434_;
}
v___jp_5435_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; uint8_t v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5437_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5436_);
v___x_5438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5438_, 0, v___y_5436_);
lean_ctor_set(v___x_5438_, 1, v___x_5437_);
v___x_5439_ = 0;
v___x_5440_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5440_, 0, v___x_5438_);
lean_ctor_set_uint8(v___x_5440_, sizeof(void*)*1, v___x_5439_);
v___x_5441_ = l_Repr_addAppParen(v___x_5440_, v_prec_5427_);
return v___x_5441_;
}
v___jp_5442_:
{
lean_object* v___x_5444_; lean_object* v___x_5445_; uint8_t v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5444_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5443_);
v___x_5445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___y_5443_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = 0;
v___x_5447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5447_, 0, v___x_5445_);
lean_ctor_set_uint8(v___x_5447_, sizeof(void*)*1, v___x_5446_);
v___x_5448_ = l_Repr_addAppParen(v___x_5447_, v_prec_5427_);
return v___x_5448_;
}
v___jp_5449_:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; uint8_t v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5451_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5450_);
v___x_5452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5452_, 0, v___y_5450_);
lean_ctor_set(v___x_5452_, 1, v___x_5451_);
v___x_5453_ = 0;
v___x_5454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5454_, 0, v___x_5452_);
lean_ctor_set_uint8(v___x_5454_, sizeof(void*)*1, v___x_5453_);
v___x_5455_ = l_Repr_addAppParen(v___x_5454_, v_prec_5427_);
return v___x_5455_;
}
v___jp_5456_:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; uint8_t v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5458_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5457_);
v___x_5459_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5459_, 0, v___y_5457_);
lean_ctor_set(v___x_5459_, 1, v___x_5458_);
v___x_5460_ = 0;
v___x_5461_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5461_, 0, v___x_5459_);
lean_ctor_set_uint8(v___x_5461_, sizeof(void*)*1, v___x_5460_);
v___x_5462_ = l_Repr_addAppParen(v___x_5461_, v_prec_5427_);
return v___x_5462_;
}
v___jp_5463_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; uint8_t v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5465_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5464_);
v___x_5466_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5466_, 0, v___y_5464_);
lean_ctor_set(v___x_5466_, 1, v___x_5465_);
v___x_5467_ = 0;
v___x_5468_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5468_, 0, v___x_5466_);
lean_ctor_set_uint8(v___x_5468_, sizeof(void*)*1, v___x_5467_);
v___x_5469_ = l_Repr_addAppParen(v___x_5468_, v_prec_5427_);
return v___x_5469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5494_, lean_object* v_prec_5495_){
_start:
{
uint8_t v_x_329__boxed_5496_; lean_object* v_res_5497_; 
v_x_329__boxed_5496_ = lean_unbox(v_x_5494_);
v_res_5497_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5496_, v_prec_5495_);
lean_dec(v_prec_5495_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5509_, lean_object* v_prec_5510_){
_start:
{
lean_object* v___y_5512_; lean_object* v___y_5519_; lean_object* v___y_5526_; 
switch(v_x_5509_)
{
case 0:
{
lean_object* v___x_5532_; uint8_t v___x_5533_; 
v___x_5532_ = lean_unsigned_to_nat(1024u);
v___x_5533_ = lean_nat_dec_le(v___x_5532_, v_prec_5510_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
v___x_5534_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5512_ = v___x_5534_;
goto v___jp_5511_;
}
else
{
lean_object* v___x_5535_; 
v___x_5535_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5512_ = v___x_5535_;
goto v___jp_5511_;
}
}
case 1:
{
lean_object* v___x_5536_; uint8_t v___x_5537_; 
v___x_5536_ = lean_unsigned_to_nat(1024u);
v___x_5537_ = lean_nat_dec_le(v___x_5536_, v_prec_5510_);
if (v___x_5537_ == 0)
{
lean_object* v___x_5538_; 
v___x_5538_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5519_ = v___x_5538_;
goto v___jp_5518_;
}
else
{
lean_object* v___x_5539_; 
v___x_5539_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5519_ = v___x_5539_;
goto v___jp_5518_;
}
}
default: 
{
lean_object* v___x_5540_; uint8_t v___x_5541_; 
v___x_5540_ = lean_unsigned_to_nat(1024u);
v___x_5541_ = lean_nat_dec_le(v___x_5540_, v_prec_5510_);
if (v___x_5541_ == 0)
{
lean_object* v___x_5542_; 
v___x_5542_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5526_ = v___x_5542_;
goto v___jp_5525_;
}
else
{
lean_object* v___x_5543_; 
v___x_5543_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5526_ = v___x_5543_;
goto v___jp_5525_;
}
}
}
v___jp_5511_:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; uint8_t v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5513_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5512_);
v___x_5514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5514_, 0, v___y_5512_);
lean_ctor_set(v___x_5514_, 1, v___x_5513_);
v___x_5515_ = 0;
v___x_5516_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5516_, 0, v___x_5514_);
lean_ctor_set_uint8(v___x_5516_, sizeof(void*)*1, v___x_5515_);
v___x_5517_ = l_Repr_addAppParen(v___x_5516_, v_prec_5510_);
return v___x_5517_;
}
v___jp_5518_:
{
lean_object* v___x_5520_; lean_object* v___x_5521_; uint8_t v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; 
v___x_5520_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5519_);
v___x_5521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5521_, 0, v___y_5519_);
lean_ctor_set(v___x_5521_, 1, v___x_5520_);
v___x_5522_ = 0;
v___x_5523_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5523_, 0, v___x_5521_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*1, v___x_5522_);
v___x_5524_ = l_Repr_addAppParen(v___x_5523_, v_prec_5510_);
return v___x_5524_;
}
v___jp_5525_:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; uint8_t v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5527_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5526_);
v___x_5528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5528_, 0, v___y_5526_);
lean_ctor_set(v___x_5528_, 1, v___x_5527_);
v___x_5529_ = 0;
v___x_5530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5530_, 0, v___x_5528_);
lean_ctor_set_uint8(v___x_5530_, sizeof(void*)*1, v___x_5529_);
v___x_5531_ = l_Repr_addAppParen(v___x_5530_, v_prec_5510_);
return v___x_5531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5544_, lean_object* v_prec_5545_){
_start:
{
uint8_t v_x_167__boxed_5546_; lean_object* v_res_5547_; 
v_x_167__boxed_5546_ = lean_unbox(v_x_5544_);
v_res_5547_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5546_, v_prec_5545_);
lean_dec(v_prec_5545_);
return v_res_5547_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5559_; lean_object* v___x_5560_; 
v___x_5559_ = lean_unsigned_to_nat(8u);
v___x_5560_ = lean_nat_to_int(v___x_5559_);
return v___x_5560_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
v___x_5570_ = lean_unsigned_to_nat(13u);
v___x_5571_ = lean_nat_to_int(v___x_5570_);
return v___x_5571_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5581_ = lean_unsigned_to_nat(10u);
v___x_5582_ = lean_nat_to_int(v___x_5581_);
return v___x_5582_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = lean_unsigned_to_nat(14u);
v___x_5587_ = lean_nat_to_int(v___x_5586_);
return v___x_5587_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5591_ = lean_unsigned_to_nat(19u);
v___x_5592_ = lean_nat_to_int(v___x_5591_);
return v___x_5592_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; 
v___x_5596_ = lean_unsigned_to_nat(20u);
v___x_5597_ = lean_nat_to_int(v___x_5596_);
return v___x_5597_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5604_ = lean_unsigned_to_nat(9u);
v___x_5605_ = lean_nat_to_int(v___x_5604_);
return v___x_5605_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5612_ = lean_unsigned_to_nat(12u);
v___x_5613_ = lean_nat_to_int(v___x_5612_);
return v___x_5613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5620_){
_start:
{
uint8_t v_zeta_5621_; uint8_t v_beta_5622_; uint8_t v_eta_5623_; uint8_t v_etaStruct_5624_; uint8_t v_iota_5625_; uint8_t v_proj_5626_; uint8_t v_decide_5627_; uint8_t v_autoUnfold_5628_; uint8_t v_failIfUnchanged_5629_; uint8_t v_unfoldPartialApp_5630_; uint8_t v_zetaDelta_5631_; uint8_t v_index_5632_; uint8_t v_zetaUnused_5633_; uint8_t v_zetaHave_5634_; uint8_t v_locals_5635_; uint8_t v_instances_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; uint8_t v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; 
v_zeta_5621_ = lean_ctor_get_uint8(v_x_5620_, 0);
v_beta_5622_ = lean_ctor_get_uint8(v_x_5620_, 1);
v_eta_5623_ = lean_ctor_get_uint8(v_x_5620_, 2);
v_etaStruct_5624_ = lean_ctor_get_uint8(v_x_5620_, 3);
v_iota_5625_ = lean_ctor_get_uint8(v_x_5620_, 4);
v_proj_5626_ = lean_ctor_get_uint8(v_x_5620_, 5);
v_decide_5627_ = lean_ctor_get_uint8(v_x_5620_, 6);
v_autoUnfold_5628_ = lean_ctor_get_uint8(v_x_5620_, 7);
v_failIfUnchanged_5629_ = lean_ctor_get_uint8(v_x_5620_, 8);
v_unfoldPartialApp_5630_ = lean_ctor_get_uint8(v_x_5620_, 9);
v_zetaDelta_5631_ = lean_ctor_get_uint8(v_x_5620_, 10);
v_index_5632_ = lean_ctor_get_uint8(v_x_5620_, 11);
v_zetaUnused_5633_ = lean_ctor_get_uint8(v_x_5620_, 12);
v_zetaHave_5634_ = lean_ctor_get_uint8(v_x_5620_, 13);
v_locals_5635_ = lean_ctor_get_uint8(v_x_5620_, 14);
v_instances_5636_ = lean_ctor_get_uint8(v_x_5620_, 15);
v___x_5637_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5638_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5639_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5640_ = lean_unsigned_to_nat(0u);
v___x_5641_ = l_Bool_repr___redArg(v_zeta_5621_);
v___x_5642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5639_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
v___x_5643_ = 0;
v___x_5644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5644_, 0, v___x_5642_);
lean_ctor_set_uint8(v___x_5644_, sizeof(void*)*1, v___x_5643_);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5638_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
v___x_5646_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5645_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = lean_box(1);
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5647_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
v___x_5650_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5649_);
lean_ctor_set(v___x_5651_, 1, v___x_5650_);
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5651_);
lean_ctor_set(v___x_5652_, 1, v___x_5637_);
v___x_5653_ = l_Bool_repr___redArg(v_beta_5622_);
v___x_5654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5639_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5655_, 0, v___x_5654_);
lean_ctor_set_uint8(v___x_5655_, sizeof(void*)*1, v___x_5643_);
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5652_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set(v___x_5657_, 1, v___x_5646_);
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
lean_ctor_set(v___x_5658_, 1, v___x_5648_);
v___x_5659_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5658_);
lean_ctor_set(v___x_5660_, 1, v___x_5659_);
v___x_5661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set(v___x_5661_, 1, v___x_5637_);
v___x_5662_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5663_ = l_Bool_repr___redArg(v_eta_5623_);
v___x_5664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5662_);
lean_ctor_set(v___x_5664_, 1, v___x_5663_);
v___x_5665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
lean_ctor_set_uint8(v___x_5665_, sizeof(void*)*1, v___x_5643_);
v___x_5666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5661_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
lean_ctor_set(v___x_5667_, 1, v___x_5646_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___x_5648_);
v___x_5669_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5668_);
lean_ctor_set(v___x_5670_, 1, v___x_5669_);
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set(v___x_5671_, 1, v___x_5637_);
v___x_5672_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5673_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5624_, v___x_5640_);
v___x_5674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5672_);
lean_ctor_set(v___x_5674_, 1, v___x_5673_);
v___x_5675_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set_uint8(v___x_5675_, sizeof(void*)*1, v___x_5643_);
v___x_5676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5671_);
lean_ctor_set(v___x_5676_, 1, v___x_5675_);
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5676_);
lean_ctor_set(v___x_5677_, 1, v___x_5646_);
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set(v___x_5678_, 1, v___x_5648_);
v___x_5679_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5678_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5680_);
lean_ctor_set(v___x_5681_, 1, v___x_5637_);
v___x_5682_ = l_Bool_repr___redArg(v_iota_5625_);
v___x_5683_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5639_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5684_, 0, v___x_5683_);
lean_ctor_set_uint8(v___x_5684_, sizeof(void*)*1, v___x_5643_);
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5681_);
lean_ctor_set(v___x_5685_, 1, v___x_5684_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
lean_ctor_set(v___x_5686_, 1, v___x_5646_);
v___x_5687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5686_);
lean_ctor_set(v___x_5687_, 1, v___x_5648_);
v___x_5688_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5687_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
lean_ctor_set(v___x_5690_, 1, v___x_5637_);
v___x_5691_ = l_Bool_repr___redArg(v_proj_5626_);
v___x_5692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5639_);
lean_ctor_set(v___x_5692_, 1, v___x_5691_);
v___x_5693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5693_, 0, v___x_5692_);
lean_ctor_set_uint8(v___x_5693_, sizeof(void*)*1, v___x_5643_);
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5690_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5646_);
v___x_5696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5695_);
lean_ctor_set(v___x_5696_, 1, v___x_5648_);
v___x_5697_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set(v___x_5699_, 1, v___x_5637_);
v___x_5700_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5701_ = l_Bool_repr___redArg(v_decide_5627_);
v___x_5702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*1, v___x_5643_);
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5699_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v___x_5646_);
v___x_5706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
lean_ctor_set(v___x_5706_, 1, v___x_5648_);
v___x_5707_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5706_);
lean_ctor_set(v___x_5708_, 1, v___x_5707_);
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set(v___x_5709_, 1, v___x_5637_);
v___x_5710_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5711_ = l_Bool_repr___redArg(v_autoUnfold_5628_);
v___x_5712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5710_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*1, v___x_5643_);
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5709_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set(v___x_5715_, 1, v___x_5646_);
v___x_5716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5715_);
lean_ctor_set(v___x_5716_, 1, v___x_5648_);
v___x_5717_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5716_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v___x_5637_);
v___x_5720_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5721_ = l_Bool_repr___redArg(v_failIfUnchanged_5629_);
v___x_5722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5720_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
lean_ctor_set_uint8(v___x_5723_, sizeof(void*)*1, v___x_5643_);
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5719_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
lean_ctor_set(v___x_5725_, 1, v___x_5646_);
v___x_5726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5725_);
lean_ctor_set(v___x_5726_, 1, v___x_5648_);
v___x_5727_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5726_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set(v___x_5729_, 1, v___x_5637_);
v___x_5730_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5731_ = l_Bool_repr___redArg(v_unfoldPartialApp_5630_);
v___x_5732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5730_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5733_, 0, v___x_5732_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*1, v___x_5643_);
v___x_5734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5729_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
lean_ctor_set(v___x_5735_, 1, v___x_5646_);
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
lean_ctor_set(v___x_5736_, 1, v___x_5648_);
v___x_5737_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5736_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
lean_ctor_set(v___x_5739_, 1, v___x_5637_);
v___x_5740_ = l_Bool_repr___redArg(v_zetaDelta_5631_);
v___x_5741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5672_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5742_, 0, v___x_5741_);
lean_ctor_set_uint8(v___x_5742_, sizeof(void*)*1, v___x_5643_);
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5739_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set(v___x_5744_, 1, v___x_5646_);
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5744_);
lean_ctor_set(v___x_5745_, 1, v___x_5648_);
v___x_5746_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set(v___x_5748_, 1, v___x_5637_);
v___x_5749_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5750_ = l_Bool_repr___redArg(v_index_5632_);
v___x_5751_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5749_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
lean_ctor_set_uint8(v___x_5752_, sizeof(void*)*1, v___x_5643_);
v___x_5753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5748_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
lean_ctor_set(v___x_5754_, 1, v___x_5646_);
v___x_5755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5754_);
lean_ctor_set(v___x_5755_, 1, v___x_5648_);
v___x_5756_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5755_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
lean_ctor_set(v___x_5758_, 1, v___x_5637_);
v___x_5759_ = l_Bool_repr___redArg(v_zetaUnused_5633_);
v___x_5760_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5710_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5761_, 0, v___x_5760_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*1, v___x_5643_);
v___x_5762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5758_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___x_5762_);
lean_ctor_set(v___x_5763_, 1, v___x_5646_);
v___x_5764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5763_);
lean_ctor_set(v___x_5764_, 1, v___x_5648_);
v___x_5765_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5764_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set(v___x_5767_, 1, v___x_5637_);
v___x_5768_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5769_ = l_Bool_repr___redArg(v_zetaHave_5634_);
v___x_5770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5768_);
lean_ctor_set(v___x_5770_, 1, v___x_5769_);
v___x_5771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5771_, 0, v___x_5770_);
lean_ctor_set_uint8(v___x_5771_, sizeof(void*)*1, v___x_5643_);
v___x_5772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5767_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5773_, 0, v___x_5772_);
lean_ctor_set(v___x_5773_, 1, v___x_5646_);
v___x_5774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5773_);
lean_ctor_set(v___x_5774_, 1, v___x_5648_);
v___x_5775_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5776_, 0, v___x_5774_);
lean_ctor_set(v___x_5776_, 1, v___x_5775_);
v___x_5777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5776_);
lean_ctor_set(v___x_5777_, 1, v___x_5637_);
v___x_5778_ = l_Bool_repr___redArg(v_locals_5635_);
v___x_5779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5700_);
lean_ctor_set(v___x_5779_, 1, v___x_5778_);
v___x_5780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5780_, 0, v___x_5779_);
lean_ctor_set_uint8(v___x_5780_, sizeof(void*)*1, v___x_5643_);
v___x_5781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5777_);
lean_ctor_set(v___x_5781_, 1, v___x_5780_);
v___x_5782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5781_);
lean_ctor_set(v___x_5782_, 1, v___x_5646_);
v___x_5783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5783_, 0, v___x_5782_);
lean_ctor_set(v___x_5783_, 1, v___x_5648_);
v___x_5784_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5785_, 0, v___x_5783_);
lean_ctor_set(v___x_5785_, 1, v___x_5784_);
v___x_5786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5785_);
lean_ctor_set(v___x_5786_, 1, v___x_5637_);
v___x_5787_ = l_Bool_repr___redArg(v_instances_5636_);
v___x_5788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5788_, 0, v___x_5672_);
lean_ctor_set(v___x_5788_, 1, v___x_5787_);
v___x_5789_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5789_, 0, v___x_5788_);
lean_ctor_set_uint8(v___x_5789_, sizeof(void*)*1, v___x_5643_);
v___x_5790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5790_, 0, v___x_5786_);
lean_ctor_set(v___x_5790_, 1, v___x_5789_);
v___x_5791_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5792_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5792_);
lean_ctor_set(v___x_5793_, 1, v___x_5790_);
v___x_5794_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5795_, 0, v___x_5793_);
lean_ctor_set(v___x_5795_, 1, v___x_5794_);
v___x_5796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5796_, 0, v___x_5791_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v___x_5797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5797_, 0, v___x_5796_);
lean_ctor_set_uint8(v___x_5797_, sizeof(void*)*1, v___x_5643_);
return v___x_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5798_);
lean_dec_ref(v_x_5798_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5800_, lean_object* v_prec_5801_){
_start:
{
lean_object* v___x_5802_; 
v___x_5802_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5800_);
return v___x_5802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5803_, lean_object* v_prec_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Lean_Meta_instReprConfig_repr(v_x_5803_, v_prec_5804_);
lean_dec(v_prec_5804_);
lean_dec_ref(v_x_5803_);
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5813_, lean_object* v_x_5814_){
_start:
{
if (lean_obj_tag(v_x_5813_) == 0)
{
lean_object* v___x_5815_; 
v___x_5815_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5815_;
}
else
{
lean_object* v_val_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5827_; 
v_val_5816_ = lean_ctor_get(v_x_5813_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_x_5813_);
if (v_isSharedCheck_5827_ == 0)
{
v___x_5818_ = v_x_5813_;
v_isShared_5819_ = v_isSharedCheck_5827_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_val_5816_);
lean_dec(v_x_5813_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5827_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5823_; 
v___x_5820_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5821_ = l_Nat_reprFast(v_val_5816_);
if (v_isShared_5819_ == 0)
{
lean_ctor_set_tag(v___x_5818_, 3);
lean_ctor_set(v___x_5818_, 0, v___x_5821_);
v___x_5823_ = v___x_5818_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5821_);
v___x_5823_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5820_);
lean_ctor_set(v___x_5824_, 1, v___x_5823_);
v___x_5825_ = l_Repr_addAppParen(v___x_5824_, v_x_5814_);
return v___x_5825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5828_, lean_object* v_x_5829_){
_start:
{
lean_object* v_res_5830_; 
v_res_5830_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5828_, v_x_5829_);
lean_dec(v_x_5829_);
return v_res_5830_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5843_ = lean_unsigned_to_nat(21u);
v___x_5844_ = lean_nat_to_int(v___x_5843_);
return v___x_5844_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = lean_unsigned_to_nat(11u);
v___x_5852_ = lean_nat_to_int(v___x_5851_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5868_ = lean_unsigned_to_nat(23u);
v___x_5869_ = lean_nat_to_int(v___x_5868_);
return v___x_5869_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5873_ = lean_unsigned_to_nat(16u);
v___x_5874_ = lean_nat_to_int(v___x_5873_);
return v___x_5874_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5881_ = lean_unsigned_to_nat(15u);
v___x_5882_ = lean_nat_to_int(v___x_5881_);
return v___x_5882_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5889_ = lean_unsigned_to_nat(17u);
v___x_5890_ = lean_nat_to_int(v___x_5889_);
return v___x_5890_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; 
v___x_5897_ = lean_unsigned_to_nat(18u);
v___x_5898_ = lean_nat_to_int(v___x_5897_);
return v___x_5898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5899_){
_start:
{
lean_object* v_maxSteps_5900_; lean_object* v_maxDischargeDepth_5901_; uint8_t v_contextual_5902_; uint8_t v_memoize_5903_; uint8_t v_singlePass_5904_; uint8_t v_zeta_5905_; uint8_t v_beta_5906_; uint8_t v_eta_5907_; uint8_t v_etaStruct_5908_; uint8_t v_iota_5909_; uint8_t v_proj_5910_; uint8_t v_decide_5911_; uint8_t v_arith_5912_; uint8_t v_autoUnfold_5913_; uint8_t v_dsimp_5914_; uint8_t v_failIfUnchanged_5915_; uint8_t v_ground_5916_; uint8_t v_unfoldPartialApp_5917_; uint8_t v_zetaDelta_5918_; uint8_t v_index_5919_; uint8_t v_implicitDefEqProofs_5920_; uint8_t v_zetaUnused_5921_; uint8_t v_catchRuntime_5922_; uint8_t v_zetaHave_5923_; uint8_t v_letToHave_5924_; uint8_t v_congrConsts_5925_; uint8_t v_bitVecOfNat_5926_; uint8_t v_warnExponents_5927_; uint8_t v_suggestions_5928_; lean_object* v_maxSuggestions_5929_; uint8_t v_locals_5930_; uint8_t v_instances_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; uint8_t v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; 
v_maxSteps_5900_ = lean_ctor_get(v_x_5899_, 0);
lean_inc(v_maxSteps_5900_);
v_maxDischargeDepth_5901_ = lean_ctor_get(v_x_5899_, 1);
lean_inc(v_maxDischargeDepth_5901_);
v_contextual_5902_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3);
v_memoize_5903_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 1);
v_singlePass_5904_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 2);
v_zeta_5905_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 3);
v_beta_5906_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 4);
v_eta_5907_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 5);
v_etaStruct_5908_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 6);
v_iota_5909_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 7);
v_proj_5910_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 8);
v_decide_5911_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 9);
v_arith_5912_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 10);
v_autoUnfold_5913_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 11);
v_dsimp_5914_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5915_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 13);
v_ground_5916_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5917_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 15);
v_zetaDelta_5918_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 16);
v_index_5919_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5920_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 18);
v_zetaUnused_5921_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 19);
v_catchRuntime_5922_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 20);
v_zetaHave_5923_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 21);
v_letToHave_5924_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 22);
v_congrConsts_5925_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5926_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 24);
v_warnExponents_5927_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 25);
v_suggestions_5928_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 26);
v_maxSuggestions_5929_ = lean_ctor_get(v_x_5899_, 2);
lean_inc(v_maxSuggestions_5929_);
v_locals_5930_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 27);
v_instances_5931_ = lean_ctor_get_uint8(v_x_5899_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5899_);
v___x_5932_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5933_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5934_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5935_ = l_Nat_reprFast(v_maxSteps_5900_);
v___x_5936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5935_);
v___x_5937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5934_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = 0;
v___x_5939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5937_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5938_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5933_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_box(1);
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set(v___x_5947_, 1, v___x_5932_);
v___x_5948_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5949_ = l_Nat_reprFast(v_maxDischargeDepth_5901_);
v___x_5950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
v___x_5951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5948_);
lean_ctor_set(v___x_5951_, 1, v___x_5950_);
v___x_5952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
lean_ctor_set_uint8(v___x_5952_, sizeof(void*)*1, v___x_5938_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5947_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set(v___x_5954_, 1, v___x_5941_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set(v___x_5955_, 1, v___x_5943_);
v___x_5956_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5955_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5932_);
v___x_5959_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5960_ = lean_unsigned_to_nat(0u);
v___x_5961_ = l_Bool_repr___redArg(v_contextual_5902_);
v___x_5962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5959_);
lean_ctor_set(v___x_5962_, 1, v___x_5961_);
v___x_5963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
lean_ctor_set_uint8(v___x_5963_, sizeof(void*)*1, v___x_5938_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5958_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set(v___x_5965_, 1, v___x_5941_);
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set(v___x_5966_, 1, v___x_5943_);
v___x_5967_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5932_);
v___x_5970_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5971_ = l_Bool_repr___redArg(v_memoize_5903_);
v___x_5972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
v___x_5973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set_uint8(v___x_5973_, sizeof(void*)*1, v___x_5938_);
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5969_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
lean_ctor_set(v___x_5975_, 1, v___x_5941_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set(v___x_5976_, 1, v___x_5943_);
v___x_5977_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5976_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5932_);
v___x_5980_ = l_Bool_repr___redArg(v_singlePass_5904_);
v___x_5981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5959_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5982_, 0, v___x_5981_);
lean_ctor_set_uint8(v___x_5982_, sizeof(void*)*1, v___x_5938_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5979_);
lean_ctor_set(v___x_5983_, 1, v___x_5982_);
v___x_5984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set(v___x_5984_, 1, v___x_5941_);
v___x_5985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
lean_ctor_set(v___x_5985_, 1, v___x_5943_);
v___x_5986_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5985_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set(v___x_5988_, 1, v___x_5932_);
v___x_5989_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5990_ = l_Bool_repr___redArg(v_zeta_5905_);
v___x_5991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5992_, 0, v___x_5991_);
lean_ctor_set_uint8(v___x_5992_, sizeof(void*)*1, v___x_5938_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5988_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set(v___x_5994_, 1, v___x_5941_);
v___x_5995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5994_);
lean_ctor_set(v___x_5995_, 1, v___x_5943_);
v___x_5996_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5995_);
lean_ctor_set(v___x_5997_, 1, v___x_5996_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5997_);
lean_ctor_set(v___x_5998_, 1, v___x_5932_);
v___x_5999_ = l_Bool_repr___redArg(v_beta_5906_);
v___x_6000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5989_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v___x_6001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set_uint8(v___x_6001_, sizeof(void*)*1, v___x_5938_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_5998_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v___x_5941_);
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set(v___x_6004_, 1, v___x_5943_);
v___x_6005_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6004_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5932_);
v___x_6008_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_6009_ = l_Bool_repr___redArg(v_eta_5907_);
v___x_6010_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6008_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set_uint8(v___x_6011_, sizeof(void*)*1, v___x_5938_);
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6007_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set(v___x_6013_, 1, v___x_5941_);
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set(v___x_6014_, 1, v___x_5943_);
v___x_6015_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5932_);
v___x_6018_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_6019_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5908_, v___x_5960_);
v___x_6020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6018_);
lean_ctor_set(v___x_6020_, 1, v___x_6019_);
v___x_6021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set_uint8(v___x_6021_, sizeof(void*)*1, v___x_5938_);
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6017_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_5941_);
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set(v___x_6024_, 1, v___x_5943_);
v___x_6025_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6024_);
lean_ctor_set(v___x_6026_, 1, v___x_6025_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_5932_);
v___x_6028_ = l_Bool_repr___redArg(v_iota_5909_);
v___x_6029_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_5989_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
lean_ctor_set_uint8(v___x_6030_, sizeof(void*)*1, v___x_5938_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6027_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_5941_);
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set(v___x_6033_, 1, v___x_5943_);
v___x_6034_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6033_);
lean_ctor_set(v___x_6035_, 1, v___x_6034_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
lean_ctor_set(v___x_6036_, 1, v___x_5932_);
v___x_6037_ = l_Bool_repr___redArg(v_proj_5910_);
v___x_6038_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_5989_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6039_, 0, v___x_6038_);
lean_ctor_set_uint8(v___x_6039_, sizeof(void*)*1, v___x_5938_);
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6036_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_5941_);
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set(v___x_6042_, 1, v___x_5943_);
v___x_6043_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6042_);
lean_ctor_set(v___x_6044_, 1, v___x_6043_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set(v___x_6045_, 1, v___x_5932_);
v___x_6046_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6047_ = l_Bool_repr___redArg(v_decide_5911_);
v___x_6048_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6046_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6049_, 0, v___x_6048_);
lean_ctor_set_uint8(v___x_6049_, sizeof(void*)*1, v___x_5938_);
v___x_6050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6045_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set(v___x_6051_, 1, v___x_5941_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6051_);
lean_ctor_set(v___x_6052_, 1, v___x_5943_);
v___x_6053_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6052_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_5932_);
v___x_6056_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6057_ = l_Bool_repr___redArg(v_arith_5912_);
v___x_6058_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6056_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set_uint8(v___x_6059_, sizeof(void*)*1, v___x_5938_);
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6055_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set(v___x_6061_, 1, v___x_5941_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
lean_ctor_set(v___x_6062_, 1, v___x_5943_);
v___x_6063_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6062_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
lean_ctor_set(v___x_6065_, 1, v___x_5932_);
v___x_6066_ = l_Bool_repr___redArg(v_autoUnfold_5913_);
v___x_6067_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_5959_);
lean_ctor_set(v___x_6067_, 1, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
lean_ctor_set_uint8(v___x_6068_, sizeof(void*)*1, v___x_5938_);
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6065_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set(v___x_6070_, 1, v___x_5941_);
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
lean_ctor_set(v___x_6071_, 1, v___x_5943_);
v___x_6072_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6071_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
lean_ctor_set(v___x_6074_, 1, v___x_5932_);
v___x_6075_ = l_Bool_repr___redArg(v_dsimp_5914_);
v___x_6076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6056_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6077_, 0, v___x_6076_);
lean_ctor_set_uint8(v___x_6077_, sizeof(void*)*1, v___x_5938_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6074_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set(v___x_6079_, 1, v___x_5941_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
lean_ctor_set(v___x_6080_, 1, v___x_5943_);
v___x_6081_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6080_);
lean_ctor_set(v___x_6082_, 1, v___x_6081_);
v___x_6083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set(v___x_6083_, 1, v___x_5932_);
v___x_6084_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6085_ = l_Bool_repr___redArg(v_failIfUnchanged_5915_);
v___x_6086_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6084_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
lean_ctor_set_uint8(v___x_6087_, sizeof(void*)*1, v___x_5938_);
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6083_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set(v___x_6089_, 1, v___x_5941_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set(v___x_6090_, 1, v___x_5943_);
v___x_6091_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6090_);
lean_ctor_set(v___x_6092_, 1, v___x_6091_);
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set(v___x_6093_, 1, v___x_5932_);
v___x_6094_ = l_Bool_repr___redArg(v_ground_5916_);
v___x_6095_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6046_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set_uint8(v___x_6096_, sizeof(void*)*1, v___x_5938_);
v___x_6097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6093_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set(v___x_6098_, 1, v___x_5941_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set(v___x_6099_, 1, v___x_5943_);
v___x_6100_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6099_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_5932_);
v___x_6103_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6104_ = l_Bool_repr___redArg(v_unfoldPartialApp_5917_);
v___x_6105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6103_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
v___x_6106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set_uint8(v___x_6106_, sizeof(void*)*1, v___x_5938_);
v___x_6107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6102_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v___x_5941_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set(v___x_6109_, 1, v___x_5943_);
v___x_6110_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6109_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6111_);
lean_ctor_set(v___x_6112_, 1, v___x_5932_);
v___x_6113_ = l_Bool_repr___redArg(v_zetaDelta_5918_);
v___x_6114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6018_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set_uint8(v___x_6115_, sizeof(void*)*1, v___x_5938_);
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6112_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_5941_);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set(v___x_6118_, 1, v___x_5943_);
v___x_6119_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6118_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set(v___x_6121_, 1, v___x_5932_);
v___x_6122_ = l_Bool_repr___redArg(v_index_5919_);
v___x_6123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6056_);
lean_ctor_set(v___x_6123_, 1, v___x_6122_);
v___x_6124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set_uint8(v___x_6124_, sizeof(void*)*1, v___x_5938_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6121_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set(v___x_6126_, 1, v___x_5941_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
lean_ctor_set(v___x_6127_, 1, v___x_5943_);
v___x_6128_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6127_);
lean_ctor_set(v___x_6129_, 1, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
lean_ctor_set(v___x_6130_, 1, v___x_5932_);
v___x_6131_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6132_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5920_);
v___x_6133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6131_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
v___x_6134_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
lean_ctor_set_uint8(v___x_6134_, sizeof(void*)*1, v___x_5938_);
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6130_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set(v___x_6136_, 1, v___x_5941_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set(v___x_6137_, 1, v___x_5943_);
v___x_6138_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6137_);
lean_ctor_set(v___x_6139_, 1, v___x_6138_);
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
lean_ctor_set(v___x_6140_, 1, v___x_5932_);
v___x_6141_ = l_Bool_repr___redArg(v_zetaUnused_5921_);
v___x_6142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_5959_);
lean_ctor_set(v___x_6142_, 1, v___x_6141_);
v___x_6143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set_uint8(v___x_6143_, sizeof(void*)*1, v___x_5938_);
v___x_6144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6140_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set(v___x_6145_, 1, v___x_5941_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
lean_ctor_set(v___x_6146_, 1, v___x_5943_);
v___x_6147_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6146_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
v___x_6149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set(v___x_6149_, 1, v___x_5932_);
v___x_6150_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6151_ = l_Bool_repr___redArg(v_catchRuntime_5922_);
v___x_6152_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6150_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
v___x_6153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6153_, 0, v___x_6152_);
lean_ctor_set_uint8(v___x_6153_, sizeof(void*)*1, v___x_5938_);
v___x_6154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6149_);
lean_ctor_set(v___x_6154_, 1, v___x_6153_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set(v___x_6155_, 1, v___x_5941_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
lean_ctor_set(v___x_6156_, 1, v___x_5943_);
v___x_6157_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6156_);
lean_ctor_set(v___x_6158_, 1, v___x_6157_);
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6158_);
lean_ctor_set(v___x_6159_, 1, v___x_5932_);
v___x_6160_ = l_Bool_repr___redArg(v_zetaHave_5923_);
v___x_6161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_5934_);
lean_ctor_set(v___x_6161_, 1, v___x_6160_);
v___x_6162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6162_, 0, v___x_6161_);
lean_ctor_set_uint8(v___x_6162_, sizeof(void*)*1, v___x_5938_);
v___x_6163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6159_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
lean_ctor_set(v___x_6164_, 1, v___x_5941_);
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6164_);
lean_ctor_set(v___x_6165_, 1, v___x_5943_);
v___x_6166_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6165_);
lean_ctor_set(v___x_6167_, 1, v___x_6166_);
v___x_6168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6167_);
lean_ctor_set(v___x_6168_, 1, v___x_5932_);
v___x_6169_ = l_Bool_repr___redArg(v_letToHave_5924_);
v___x_6170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6018_);
lean_ctor_set(v___x_6170_, 1, v___x_6169_);
v___x_6171_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
lean_ctor_set_uint8(v___x_6171_, sizeof(void*)*1, v___x_5938_);
v___x_6172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6168_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set(v___x_6173_, 1, v___x_5941_);
v___x_6174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6173_);
lean_ctor_set(v___x_6174_, 1, v___x_5943_);
v___x_6175_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6174_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set(v___x_6177_, 1, v___x_5932_);
v___x_6178_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6179_ = l_Bool_repr___redArg(v_congrConsts_5925_);
v___x_6180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6178_);
lean_ctor_set(v___x_6180_, 1, v___x_6179_);
v___x_6181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
lean_ctor_set_uint8(v___x_6181_, sizeof(void*)*1, v___x_5938_);
v___x_6182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6177_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
v___x_6183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6182_);
lean_ctor_set(v___x_6183_, 1, v___x_5941_);
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6183_);
lean_ctor_set(v___x_6184_, 1, v___x_5943_);
v___x_6185_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6184_);
lean_ctor_set(v___x_6186_, 1, v___x_6185_);
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___x_5932_);
v___x_6188_ = l_Bool_repr___redArg(v_bitVecOfNat_5926_);
v___x_6189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6178_);
lean_ctor_set(v___x_6189_, 1, v___x_6188_);
v___x_6190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6190_, 0, v___x_6189_);
lean_ctor_set_uint8(v___x_6190_, sizeof(void*)*1, v___x_5938_);
v___x_6191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6187_);
lean_ctor_set(v___x_6191_, 1, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set(v___x_6192_, 1, v___x_5941_);
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6192_);
lean_ctor_set(v___x_6193_, 1, v___x_5943_);
v___x_6194_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6193_);
lean_ctor_set(v___x_6195_, 1, v___x_6194_);
v___x_6196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
lean_ctor_set(v___x_6196_, 1, v___x_5932_);
v___x_6197_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6198_ = l_Bool_repr___redArg(v_warnExponents_5927_);
v___x_6199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6197_);
lean_ctor_set(v___x_6199_, 1, v___x_6198_);
v___x_6200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6200_, 0, v___x_6199_);
lean_ctor_set_uint8(v___x_6200_, sizeof(void*)*1, v___x_5938_);
v___x_6201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6196_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
lean_ctor_set(v___x_6202_, 1, v___x_5941_);
v___x_6203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set(v___x_6203_, 1, v___x_5943_);
v___x_6204_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6205_, 0, v___x_6203_);
lean_ctor_set(v___x_6205_, 1, v___x_6204_);
v___x_6206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6205_);
lean_ctor_set(v___x_6206_, 1, v___x_5932_);
v___x_6207_ = l_Bool_repr___redArg(v_suggestions_5928_);
v___x_6208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6178_);
lean_ctor_set(v___x_6208_, 1, v___x_6207_);
v___x_6209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6209_, 0, v___x_6208_);
lean_ctor_set_uint8(v___x_6209_, sizeof(void*)*1, v___x_5938_);
v___x_6210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6206_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
lean_ctor_set(v___x_6211_, 1, v___x_5941_);
v___x_6212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6211_);
lean_ctor_set(v___x_6212_, 1, v___x_5943_);
v___x_6213_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6212_);
lean_ctor_set(v___x_6214_, 1, v___x_6213_);
v___x_6215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6214_);
lean_ctor_set(v___x_6215_, 1, v___x_5932_);
v___x_6216_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6217_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5929_, v___x_5960_);
v___x_6218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6216_);
lean_ctor_set(v___x_6218_, 1, v___x_6217_);
v___x_6219_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6219_, 0, v___x_6218_);
lean_ctor_set_uint8(v___x_6219_, sizeof(void*)*1, v___x_5938_);
v___x_6220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6220_, 0, v___x_6215_);
lean_ctor_set(v___x_6220_, 1, v___x_6219_);
v___x_6221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6220_);
lean_ctor_set(v___x_6221_, 1, v___x_5941_);
v___x_6222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6222_, 0, v___x_6221_);
lean_ctor_set(v___x_6222_, 1, v___x_5943_);
v___x_6223_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6224_, 0, v___x_6222_);
lean_ctor_set(v___x_6224_, 1, v___x_6223_);
v___x_6225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6224_);
lean_ctor_set(v___x_6225_, 1, v___x_5932_);
v___x_6226_ = l_Bool_repr___redArg(v_locals_5930_);
v___x_6227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6227_, 0, v___x_6046_);
lean_ctor_set(v___x_6227_, 1, v___x_6226_);
v___x_6228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6228_, 0, v___x_6227_);
lean_ctor_set_uint8(v___x_6228_, sizeof(void*)*1, v___x_5938_);
v___x_6229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6225_);
lean_ctor_set(v___x_6229_, 1, v___x_6228_);
v___x_6230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6230_, 0, v___x_6229_);
lean_ctor_set(v___x_6230_, 1, v___x_5941_);
v___x_6231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6231_, 0, v___x_6230_);
lean_ctor_set(v___x_6231_, 1, v___x_5943_);
v___x_6232_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6233_, 0, v___x_6231_);
lean_ctor_set(v___x_6233_, 1, v___x_6232_);
v___x_6234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6233_);
lean_ctor_set(v___x_6234_, 1, v___x_5932_);
v___x_6235_ = l_Bool_repr___redArg(v_instances_5931_);
v___x_6236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6236_, 0, v___x_6018_);
lean_ctor_set(v___x_6236_, 1, v___x_6235_);
v___x_6237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6237_, 0, v___x_6236_);
lean_ctor_set_uint8(v___x_6237_, sizeof(void*)*1, v___x_5938_);
v___x_6238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6238_, 0, v___x_6234_);
lean_ctor_set(v___x_6238_, 1, v___x_6237_);
v___x_6239_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6240_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6241_, 0, v___x_6240_);
lean_ctor_set(v___x_6241_, 1, v___x_6238_);
v___x_6242_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6243_, 0, v___x_6241_);
lean_ctor_set(v___x_6243_, 1, v___x_6242_);
v___x_6244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6244_, 0, v___x_6239_);
lean_ctor_set(v___x_6244_, 1, v___x_6243_);
v___x_6245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6245_, 0, v___x_6244_);
lean_ctor_set_uint8(v___x_6245_, sizeof(void*)*1, v___x_5938_);
return v___x_6245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6246_, lean_object* v_prec_6247_){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6246_);
return v___x_6248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6249_, lean_object* v_prec_6250_){
_start:
{
lean_object* v_res_6251_; 
v_res_6251_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6249_, v_prec_6250_);
lean_dec(v_prec_6250_);
return v_res_6251_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6254_, lean_object* v_x_6255_){
_start:
{
if (lean_obj_tag(v_x_6255_) == 0)
{
uint8_t v___x_6256_; 
v___x_6256_ = 0;
return v___x_6256_;
}
else
{
lean_object* v_head_6257_; lean_object* v_tail_6258_; uint8_t v___x_6259_; 
v_head_6257_ = lean_ctor_get(v_x_6255_, 0);
v_tail_6258_ = lean_ctor_get(v_x_6255_, 1);
v___x_6259_ = lean_nat_dec_eq(v_a_6254_, v_head_6257_);
if (v___x_6259_ == 0)
{
v_x_6255_ = v_tail_6258_;
goto _start;
}
else
{
return v___x_6259_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6261_, lean_object* v_x_6262_){
_start:
{
uint8_t v_res_6263_; lean_object* v_r_6264_; 
v_res_6263_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6261_, v_x_6262_);
lean_dec(v_x_6262_);
lean_dec(v_a_6261_);
v_r_6264_ = lean_box(v_res_6263_);
return v_r_6264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6265_, lean_object* v_x_6266_){
_start:
{
switch(lean_obj_tag(v_x_6265_))
{
case 0:
{
uint8_t v___x_6267_; 
v___x_6267_ = 1;
return v___x_6267_;
}
case 1:
{
lean_object* v_idxs_6268_; uint8_t v___x_6269_; 
v_idxs_6268_ = lean_ctor_get(v_x_6265_, 0);
v___x_6269_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6266_, v_idxs_6268_);
return v___x_6269_;
}
default: 
{
lean_object* v_idxs_6270_; uint8_t v___x_6271_; 
v_idxs_6270_ = lean_ctor_get(v_x_6265_, 0);
v___x_6271_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6266_, v_idxs_6270_);
if (v___x_6271_ == 0)
{
uint8_t v___x_6272_; 
v___x_6272_ = 1;
return v___x_6272_;
}
else
{
uint8_t v___x_6273_; 
v___x_6273_ = 0;
return v___x_6273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6274_, lean_object* v_x_6275_){
_start:
{
uint8_t v_res_6276_; lean_object* v_r_6277_; 
v_res_6276_ = l_Lean_Meta_Occurrences_contains(v_x_6274_, v_x_6275_);
lean_dec(v_x_6275_);
lean_dec(v_x_6274_);
v_r_6277_ = lean_box(v_res_6276_);
return v_r_6277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6278_){
_start:
{
if (lean_obj_tag(v_x_6278_) == 0)
{
uint8_t v___x_6279_; 
v___x_6279_ = 1;
return v___x_6279_;
}
else
{
uint8_t v___x_6280_; 
v___x_6280_ = 0;
return v___x_6280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6281_){
_start:
{
uint8_t v_res_6282_; lean_object* v_r_6283_; 
v_res_6282_ = l_Lean_Meta_Occurrences_isAll(v_x_6281_);
lean_dec(v_x_6281_);
v_r_6283_ = lean_box(v_res_6282_);
return v_r_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6284_){
_start:
{
switch(v_x_6284_)
{
case 0:
{
lean_object* v___x_6285_; 
v___x_6285_ = lean_unsigned_to_nat(0u);
return v___x_6285_;
}
case 1:
{
lean_object* v___x_6286_; 
v___x_6286_ = lean_unsigned_to_nat(1u);
return v___x_6286_;
}
default: 
{
lean_object* v___x_6287_; 
v___x_6287_ = lean_unsigned_to_nat(2u);
return v___x_6287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6288_){
_start:
{
uint8_t v_x_boxed_6289_; lean_object* v_res_6290_; 
v_x_boxed_6289_ = lean_unbox(v_x_6288_);
v_res_6290_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6289_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6291_){
_start:
{
lean_inc(v_k_6291_);
return v_k_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6292_){
_start:
{
lean_object* v_res_6293_; 
v_res_6293_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6292_);
lean_dec(v_k_6292_);
return v_res_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6294_, lean_object* v_ctorIdx_6295_, uint8_t v_t_6296_, lean_object* v_h_6297_, lean_object* v_k_6298_){
_start:
{
lean_inc(v_k_6298_);
return v_k_6298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6299_, lean_object* v_ctorIdx_6300_, lean_object* v_t_6301_, lean_object* v_h_6302_, lean_object* v_k_6303_){
_start:
{
uint8_t v_t_boxed_6304_; lean_object* v_res_6305_; 
v_t_boxed_6304_ = lean_unbox(v_t_6301_);
v_res_6305_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6299_, v_ctorIdx_6300_, v_t_boxed_6304_, v_h_6302_, v_k_6303_);
lean_dec(v_k_6303_);
lean_dec(v_ctorIdx_6300_);
return v_res_6305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6306_){
_start:
{
lean_inc(v_nonDependentFirst_6306_);
return v_nonDependentFirst_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6307_){
_start:
{
lean_object* v_res_6308_; 
v_res_6308_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6307_);
lean_dec(v_nonDependentFirst_6307_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6309_, uint8_t v_t_6310_, lean_object* v_h_6311_, lean_object* v_nonDependentFirst_6312_){
_start:
{
lean_inc(v_nonDependentFirst_6312_);
return v_nonDependentFirst_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6313_, lean_object* v_t_6314_, lean_object* v_h_6315_, lean_object* v_nonDependentFirst_6316_){
_start:
{
uint8_t v_t_boxed_6317_; lean_object* v_res_6318_; 
v_t_boxed_6317_ = lean_unbox(v_t_6314_);
v_res_6318_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6313_, v_t_boxed_6317_, v_h_6315_, v_nonDependentFirst_6316_);
lean_dec(v_nonDependentFirst_6316_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6319_){
_start:
{
lean_inc(v_nonDependentOnly_6319_);
return v_nonDependentOnly_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6320_){
_start:
{
lean_object* v_res_6321_; 
v_res_6321_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6320_);
lean_dec(v_nonDependentOnly_6320_);
return v_res_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6322_, uint8_t v_t_6323_, lean_object* v_h_6324_, lean_object* v_nonDependentOnly_6325_){
_start:
{
lean_inc(v_nonDependentOnly_6325_);
return v_nonDependentOnly_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6326_, lean_object* v_t_6327_, lean_object* v_h_6328_, lean_object* v_nonDependentOnly_6329_){
_start:
{
uint8_t v_t_boxed_6330_; lean_object* v_res_6331_; 
v_t_boxed_6330_ = lean_unbox(v_t_6327_);
v_res_6331_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6326_, v_t_boxed_6330_, v_h_6328_, v_nonDependentOnly_6329_);
lean_dec(v_nonDependentOnly_6329_);
return v_res_6331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6332_){
_start:
{
lean_inc(v_all_6332_);
return v_all_6332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6333_){
_start:
{
lean_object* v_res_6334_; 
v_res_6334_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6333_);
lean_dec(v_all_6333_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6335_, uint8_t v_t_6336_, lean_object* v_h_6337_, lean_object* v_all_6338_){
_start:
{
lean_inc(v_all_6338_);
return v_all_6338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6339_, lean_object* v_t_6340_, lean_object* v_h_6341_, lean_object* v_all_6342_){
_start:
{
uint8_t v_t_boxed_6343_; lean_object* v_res_6344_; 
v_t_boxed_6343_ = lean_unbox(v_t_6340_);
v_res_6344_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6339_, v_t_boxed_6343_, v_h_6341_, v_all_6342_);
lean_dec(v_all_6342_);
return v_res_6344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6358_){
_start:
{
lean_object* v___x_6359_; uint8_t v___x_6360_; 
v___x_6359_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6358_);
v___x_6360_ = l_Lean_Syntax_isOfKind(v_c_6358_, v___x_6359_);
if (v___x_6360_ == 0)
{
lean_object* v___x_6361_; uint8_t v___x_6362_; 
v___x_6361_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6358_);
v___x_6362_ = l_Lean_Syntax_isOfKind(v_c_6358_, v___x_6361_);
if (v___x_6362_ == 0)
{
lean_object* v___x_6363_; uint8_t v___x_6364_; 
v___x_6363_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6358_);
v___x_6364_ = l_Lean_Syntax_isOfKind(v_c_6358_, v___x_6363_);
if (v___x_6364_ == 0)
{
lean_object* v___x_6365_; 
lean_dec(v_c_6358_);
v___x_6365_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6365_;
}
else
{
lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6366_ = lean_unsigned_to_nat(1u);
v___x_6367_ = lean_mk_empty_array_with_capacity(v___x_6366_);
v___x_6368_ = lean_array_push(v___x_6367_, v_c_6358_);
return v___x_6368_;
}
}
else
{
lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; 
v___x_6369_ = lean_unsigned_to_nat(0u);
v___x_6370_ = l_Lean_Syntax_getArg(v_c_6358_, v___x_6369_);
lean_dec(v_c_6358_);
v___x_6371_ = l_Lean_Syntax_getArgs(v___x_6370_);
lean_dec(v___x_6370_);
return v___x_6371_;
}
}
else
{
lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; uint8_t v___x_6376_; 
v___x_6372_ = l_Lean_Syntax_getArgs(v_c_6358_);
lean_dec(v_c_6358_);
v___x_6373_ = lean_unsigned_to_nat(0u);
v___x_6374_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6375_ = lean_array_get_size(v___x_6372_);
v___x_6376_ = lean_nat_dec_lt(v___x_6373_, v___x_6375_);
if (v___x_6376_ == 0)
{
lean_dec_ref(v___x_6372_);
return v___x_6374_;
}
else
{
size_t v___x_6377_; size_t v___x_6378_; lean_object* v___x_6379_; 
v___x_6377_ = ((size_t)0ULL);
v___x_6378_ = lean_usize_of_nat(v___x_6375_);
v___x_6379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6372_, v___x_6377_, v___x_6378_, v___x_6374_);
lean_dec_ref(v___x_6372_);
return v___x_6379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6380_, size_t v_i_6381_, size_t v_stop_6382_, lean_object* v_b_6383_){
_start:
{
uint8_t v___x_6384_; 
v___x_6384_ = lean_usize_dec_eq(v_i_6381_, v_stop_6382_);
if (v___x_6384_ == 0)
{
lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; size_t v___x_6388_; size_t v___x_6389_; 
v___x_6385_ = lean_array_uget_borrowed(v_as_6380_, v_i_6381_);
lean_inc(v___x_6385_);
v___x_6386_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6385_);
v___x_6387_ = l_Array_append___redArg(v_b_6383_, v___x_6386_);
lean_dec_ref(v___x_6386_);
v___x_6388_ = ((size_t)1ULL);
v___x_6389_ = lean_usize_add(v_i_6381_, v___x_6388_);
v_i_6381_ = v___x_6389_;
v_b_6383_ = v___x_6387_;
goto _start;
}
else
{
return v_b_6383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6391_, lean_object* v_i_6392_, lean_object* v_stop_6393_, lean_object* v_b_6394_){
_start:
{
size_t v_i_boxed_6395_; size_t v_stop_boxed_6396_; lean_object* v_res_6397_; 
v_i_boxed_6395_ = lean_unbox_usize(v_i_6392_);
lean_dec(v_i_6392_);
v_stop_boxed_6396_ = lean_unbox_usize(v_stop_6393_);
lean_dec(v_stop_6393_);
v_res_6397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6391_, v_i_boxed_6395_, v_stop_boxed_6396_, v_b_6394_);
lean_dec_ref(v_as_6391_);
return v_res_6397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6398_){
_start:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6399_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6400_ = lean_box(2);
v___x_6401_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6402_, 0, v___x_6400_);
lean_ctor_set(v___x_6402_, 1, v___x_6401_);
lean_ctor_set(v___x_6402_, 2, v_items_6398_);
v___x_6403_ = l_Lean_Syntax_node1(v___x_6400_, v___x_6399_, v___x_6402_);
return v___x_6403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6404_, lean_object* v_cfg_x27_6405_){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; 
v___x_6406_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6404_);
v___x_6407_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6405_);
v___x_6408_ = l_Array_append___redArg(v___x_6406_, v___x_6407_);
lean_dec_ref(v___x_6407_);
v___x_6409_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6408_);
return v___x_6409_;
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
