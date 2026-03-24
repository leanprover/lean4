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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
uint32_t lean_string_front(lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* lean_nat_pred(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_string_trim(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_toolchain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__3;
static lean_once_cell_t l_Lean_toolchain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__4;
static lean_once_cell_t l_Lean_toolchain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__5;
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
LEAN_EXPORT uint8_t lean_is_inaccessible_user_name(lean_object*);
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
LEAN_EXPORT lean_object* lean_name_append_before(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lean_mk_syntax_ident(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value;
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object*);
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
static lean_object* _init_l_Lean_toolchain___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = l_Lean_versionStringCore;
v___x_91_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__4(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_94_ = lean_obj_once(&l_Lean_toolchain___closed__3, &l_Lean_toolchain___closed__3_once, _init_l_Lean_toolchain___closed__3);
v___x_95_ = lean_string_append(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__5(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = l_Lean_version_specialDesc;
v___x_97_ = lean_obj_once(&l_Lean_toolchain___closed__4, &l_Lean_toolchain___closed__4_once, _init_l_Lean_toolchain___closed__4);
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_toolchain(void){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_100_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = l_Lean_version_isRelease;
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_toolchain___closed__2, &l_Lean_toolchain___closed__2_once, _init_l_Lean_toolchain___closed__2);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
return v___x_103_;
}
}
else
{
uint8_t v___x_104_; 
v___x_104_ = l_Lean_version_isRelease;
if (v___x_104_ == 0)
{
return v___x_99_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_toolchain___closed__3, &l_Lean_toolchain___closed__3_once, _init_l_Lean_toolchain___closed__3);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object* v_u_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = lean_internal_is_stage0(v_u_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object* v_u_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = lean_internal_has_llvm_backend(v_u_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t v_c_114_){
_start:
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 913;
v___x_116_ = lean_uint32_dec_le(v___x_115_, v_c_114_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 989;
v___x_118_ = lean_uint32_dec_le(v_c_114_, v___x_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object* v_c_119_){
_start:
{
uint32_t v_c_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_c_boxed_120_ = lean_unbox_uint32(v_c_119_);
lean_dec(v_c_119_);
v_res_121_ = l_Lean_isGreek(v_c_boxed_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t v_c_123_){
_start:
{
uint8_t v___y_130_; uint8_t v___y_136_; uint8_t v___y_142_; uint8_t v___y_148_; uint8_t v___y_154_; uint8_t v___y_165_; uint8_t v___y_176_; uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 945;
v___x_180_ = lean_uint32_dec_le(v___x_179_, v_c_123_);
if (v___x_180_ == 0)
{
v___y_176_ = v___x_180_;
goto v___jp_175_;
}
else
{
uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = 969;
v___x_182_ = lean_uint32_dec_le(v_c_123_, v___x_181_);
v___y_176_ = v___x_182_;
goto v___jp_175_;
}
v___jp_124_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 256;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_c_123_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 383;
v___x_128_ = lean_uint32_dec_le(v_c_123_, v___x_127_);
return v___x_128_;
}
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 215;
v___x_132_ = lean_uint32_dec_eq(v_c_123_, v___x_131_);
if (v___x_132_ == 0)
{
uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_133_ = 247;
v___x_134_ = lean_uint32_dec_eq(v_c_123_, v___x_133_);
if (v___x_134_ == 0)
{
return v___y_130_;
}
else
{
goto v___jp_124_;
}
}
else
{
goto v___jp_124_;
}
}
}
v___jp_135_:
{
if (v___y_136_ == 0)
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 192;
v___x_138_ = lean_uint32_dec_le(v___x_137_, v_c_123_);
if (v___x_138_ == 0)
{
v___y_130_ = v___x_138_;
goto v___jp_129_;
}
else
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 255;
v___x_140_ = lean_uint32_dec_le(v_c_123_, v___x_139_);
v___y_130_ = v___x_140_;
goto v___jp_129_;
}
}
else
{
return v___y_136_;
}
}
v___jp_141_:
{
if (v___y_142_ == 0)
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 119964;
v___x_144_ = lean_uint32_dec_le(v___x_143_, v_c_123_);
if (v___x_144_ == 0)
{
v___y_136_ = v___x_144_;
goto v___jp_135_;
}
else
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 120223;
v___x_146_ = lean_uint32_dec_le(v_c_123_, v___x_145_);
v___y_136_ = v___x_146_;
goto v___jp_135_;
}
}
else
{
return v___y_142_;
}
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 8448;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_123_);
if (v___x_150_ == 0)
{
v___y_142_ = v___x_150_;
goto v___jp_141_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 8527;
v___x_152_ = lean_uint32_dec_le(v_c_123_, v___x_151_);
v___y_142_ = v___x_152_;
goto v___jp_141_;
}
}
else
{
return v___y_148_;
}
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 7936;
v___x_156_ = lean_uint32_dec_le(v___x_155_, v_c_123_);
if (v___x_156_ == 0)
{
v___y_148_ = v___x_156_;
goto v___jp_147_;
}
else
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 8190;
v___x_158_ = lean_uint32_dec_le(v_c_123_, v___x_157_);
v___y_148_ = v___x_158_;
goto v___jp_147_;
}
}
else
{
return v___y_154_;
}
}
v___jp_159_:
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 970;
v___x_161_ = lean_uint32_dec_le(v___x_160_, v_c_123_);
if (v___x_161_ == 0)
{
v___y_154_ = v___x_161_;
goto v___jp_153_;
}
else
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 1019;
v___x_163_ = lean_uint32_dec_le(v_c_123_, v___x_162_);
v___y_154_ = v___x_163_;
goto v___jp_153_;
}
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
goto v___jp_159_;
}
else
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 928;
v___x_167_ = lean_uint32_dec_eq(v_c_123_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 931;
v___x_169_ = lean_uint32_dec_eq(v_c_123_, v___x_168_);
if (v___x_169_ == 0)
{
return v___y_165_;
}
else
{
goto v___jp_159_;
}
}
else
{
goto v___jp_159_;
}
}
}
v___jp_170_:
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 913;
v___x_172_ = lean_uint32_dec_le(v___x_171_, v_c_123_);
if (v___x_172_ == 0)
{
v___y_165_ = v___x_172_;
goto v___jp_164_;
}
else
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 937;
v___x_174_ = lean_uint32_dec_le(v_c_123_, v___x_173_);
v___y_165_ = v___x_174_;
goto v___jp_164_;
}
}
v___jp_175_:
{
if (v___y_176_ == 0)
{
goto v___jp_170_;
}
else
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 955;
v___x_178_ = lean_uint32_dec_eq(v_c_123_, v___x_177_);
if (v___x_178_ == 0)
{
return v___y_176_;
}
else
{
goto v___jp_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_183_){
_start:
{
uint32_t v_c_boxed_184_; uint8_t v_res_185_; lean_object* v_r_186_; 
v_c_boxed_184_ = lean_unbox_uint32(v_c_183_);
lean_dec(v_c_183_);
v_res_185_ = l_Lean_isLetterLike(v_c_boxed_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t v_c_187_){
_start:
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 8320;
v___x_189_ = lean_uint32_dec_le(v___x_188_, v_c_187_);
if (v___x_189_ == 0)
{
return v___x_189_;
}
else
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 8329;
v___x_191_ = lean_uint32_dec_le(v_c_187_, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_192_){
_start:
{
uint32_t v_c_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_c_boxed_193_ = lean_unbox_uint32(v_c_192_);
lean_dec(v_c_192_);
v_res_194_ = l_Lean_isNumericSubscript(v_c_boxed_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_196_){
_start:
{
uint8_t v___y_198_; uint8_t v___y_202_; uint8_t v___y_208_; uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 8320;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v_c_196_);
if (v___x_214_ == 0)
{
v___y_208_ = v___x_214_;
goto v___jp_207_;
}
else
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 8329;
v___x_216_ = lean_uint32_dec_le(v_c_196_, v___x_215_);
v___y_208_ = v___x_216_;
goto v___jp_207_;
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 11388;
v___x_200_ = lean_uint32_dec_eq(v_c_196_, v___x_199_);
return v___x_200_;
}
else
{
return v___y_198_;
}
}
v___jp_201_:
{
if (v___y_202_ == 0)
{
uint32_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = 7522;
v___x_204_ = lean_uint32_dec_le(v___x_203_, v_c_196_);
if (v___x_204_ == 0)
{
v___y_198_ = v___x_204_;
goto v___jp_197_;
}
else
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 7530;
v___x_206_ = lean_uint32_dec_le(v_c_196_, v___x_205_);
v___y_198_ = v___x_206_;
goto v___jp_197_;
}
}
else
{
return v___y_202_;
}
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
uint32_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 8336;
v___x_210_ = lean_uint32_dec_le(v___x_209_, v_c_196_);
if (v___x_210_ == 0)
{
v___y_202_ = v___x_210_;
goto v___jp_201_;
}
else
{
uint32_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 8348;
v___x_212_ = lean_uint32_dec_le(v_c_196_, v___x_211_);
v___y_202_ = v___x_212_;
goto v___jp_201_;
}
}
else
{
return v___y_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_217_){
_start:
{
uint32_t v_c_boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_c_boxed_218_ = lean_unbox_uint32(v_c_217_);
lean_dec(v_c_217_);
v_res_219_ = l_Lean_isSubScriptAlnum(v_c_boxed_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t v_c_221_){
_start:
{
uint8_t v___y_223_; uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 65;
v___x_233_ = lean_uint32_dec_le(v___x_232_, v_c_221_);
if (v___x_233_ == 0)
{
goto v___jp_227_;
}
else
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 90;
v___x_235_ = lean_uint32_dec_le(v_c_221_, v___x_234_);
if (v___x_235_ == 0)
{
goto v___jp_227_;
}
else
{
return v___x_235_;
}
}
v___jp_222_:
{
if (v___y_223_ == 0)
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 95;
v___x_225_ = lean_uint32_dec_eq(v_c_221_, v___x_224_);
if (v___x_225_ == 0)
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_isLetterLike(v_c_221_);
return v___x_226_;
}
else
{
return v___x_225_;
}
}
else
{
return v___y_223_;
}
}
v___jp_227_:
{
uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = 97;
v___x_229_ = lean_uint32_dec_le(v___x_228_, v_c_221_);
if (v___x_229_ == 0)
{
v___y_223_ = v___x_229_;
goto v___jp_222_;
}
else
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 122;
v___x_231_ = lean_uint32_dec_le(v_c_221_, v___x_230_);
v___y_223_ = v___x_231_;
goto v___jp_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_236_){
_start:
{
uint32_t v_c_boxed_237_; uint8_t v_res_238_; lean_object* v_r_239_; 
v_c_boxed_237_ = lean_unbox_uint32(v_c_236_);
lean_dec(v_c_236_);
v_res_238_ = l_Lean_isIdFirst(v_c_boxed_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0(void){
_start:
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 65;
v___x_241_ = lean_uint32_to_uint8(v___x_240_);
return v___x_241_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1(void){
_start:
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 90;
v___x_243_ = lean_uint32_to_uint8(v___x_242_);
return v___x_243_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2(void){
_start:
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 97;
v___x_245_ = lean_uint32_to_uint8(v___x_244_);
return v___x_245_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3(void){
_start:
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 122;
v___x_247_ = lean_uint32_to_uint8(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_248_){
_start:
{
uint8_t v___y_250_; uint8_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_256_ = lean_uint8_dec_le(v___x_255_, v_c_248_);
if (v___x_256_ == 0)
{
v___y_250_ = v___x_256_;
goto v___jp_249_;
}
else
{
uint8_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_258_ = lean_uint8_dec_le(v_c_248_, v___x_257_);
v___y_250_ = v___x_258_;
goto v___jp_249_;
}
v___jp_249_:
{
if (v___y_250_ == 0)
{
uint8_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_252_ = lean_uint8_dec_le(v___x_251_, v_c_248_);
if (v___x_252_ == 0)
{
return v___x_252_;
}
else
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_254_ = lean_uint8_dec_le(v_c_248_, v___x_253_);
return v___x_254_;
}
}
else
{
return v___y_250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_259_){
_start:
{
uint8_t v_c_boxed_260_; uint8_t v_res_261_; lean_object* v_r_262_; 
v_c_boxed_260_ = lean_unbox(v_c_259_);
v_res_261_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0(void){
_start:
{
uint32_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 95;
v___x_264_ = lean_uint32_to_uint8(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_265_){
_start:
{
uint8_t v___y_267_; uint8_t v___y_271_; uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_277_ = lean_uint8_dec_le(v___x_276_, v_c_265_);
if (v___x_277_ == 0)
{
v___y_271_ = v___x_277_;
goto v___jp_270_;
}
else
{
uint8_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_279_ = lean_uint8_dec_le(v_c_265_, v___x_278_);
v___y_271_ = v___x_279_;
goto v___jp_270_;
}
v___jp_266_:
{
if (v___y_267_ == 0)
{
uint8_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_269_ = lean_uint8_dec_eq(v_c_265_, v___x_268_);
return v___x_269_;
}
else
{
return v___y_267_;
}
}
v___jp_270_:
{
if (v___y_271_ == 0)
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_273_ = lean_uint8_dec_le(v___x_272_, v_c_265_);
if (v___x_273_ == 0)
{
v___y_267_ = v___x_273_;
goto v___jp_266_;
}
else
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_275_ = lean_uint8_dec_le(v_c_265_, v___x_274_);
v___y_267_ = v___x_275_;
goto v___jp_266_;
}
}
else
{
return v___y_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_280_){
_start:
{
uint8_t v_c_boxed_281_; uint8_t v_res_282_; lean_object* v_r_283_; 
v_c_boxed_281_ = lean_unbox(v_c_280_);
v_res_282_ = l_Lean_isIdFirstAscii(v_c_boxed_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0(void){
_start:
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 48;
v___x_285_ = lean_uint32_to_uint8(v___x_284_);
return v___x_285_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1(void){
_start:
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 57;
v___x_287_ = lean_uint32_to_uint8(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_288_){
_start:
{
uint8_t v___y_290_; uint8_t v___y_296_; uint8_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_302_ = lean_uint8_dec_le(v___x_301_, v_c_288_);
if (v___x_302_ == 0)
{
v___y_296_ = v___x_302_;
goto v___jp_295_;
}
else
{
uint8_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_304_ = lean_uint8_dec_le(v_c_288_, v___x_303_);
v___y_296_ = v___x_304_;
goto v___jp_295_;
}
v___jp_289_:
{
if (v___y_290_ == 0)
{
uint8_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_292_ = lean_uint8_dec_le(v___x_291_, v_c_288_);
if (v___x_292_ == 0)
{
return v___x_292_;
}
else
{
uint8_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_294_ = lean_uint8_dec_le(v_c_288_, v___x_293_);
return v___x_294_;
}
}
else
{
return v___y_290_;
}
}
v___jp_295_:
{
if (v___y_296_ == 0)
{
uint8_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_298_ = lean_uint8_dec_le(v___x_297_, v_c_288_);
if (v___x_298_ == 0)
{
v___y_290_ = v___x_298_;
goto v___jp_289_;
}
else
{
uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_300_ = lean_uint8_dec_le(v_c_288_, v___x_299_);
v___y_290_ = v___x_300_;
goto v___jp_289_;
}
}
else
{
return v___y_296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_305_){
_start:
{
uint8_t v_c_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_c_boxed_306_ = lean_unbox(v_c_305_);
v_res_307_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_309_){
_start:
{
uint8_t v___y_311_; uint8_t v___y_323_; uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = 65;
v___x_334_ = lean_uint32_dec_le(v___x_333_, v_c_309_);
if (v___x_334_ == 0)
{
goto v___jp_328_;
}
else
{
uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 90;
v___x_336_ = lean_uint32_dec_le(v_c_309_, v___x_335_);
if (v___x_336_ == 0)
{
goto v___jp_328_;
}
else
{
return v___x_336_;
}
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 95;
v___x_313_ = lean_uint32_dec_eq(v_c_309_, v___x_312_);
if (v___x_313_ == 0)
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 39;
v___x_315_ = lean_uint32_dec_eq(v_c_309_, v___x_314_);
if (v___x_315_ == 0)
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 33;
v___x_317_ = lean_uint32_dec_eq(v_c_309_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 63;
v___x_319_ = lean_uint32_dec_eq(v_c_309_, v___x_318_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_isLetterLike(v_c_309_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_isSubScriptAlnum(v_c_309_);
return v___x_321_;
}
else
{
return v___x_320_;
}
}
else
{
return v___x_319_;
}
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
else
{
return v___y_311_;
}
}
v___jp_322_:
{
if (v___y_323_ == 0)
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 48;
v___x_325_ = lean_uint32_dec_le(v___x_324_, v_c_309_);
if (v___x_325_ == 0)
{
v___y_311_ = v___x_325_;
goto v___jp_310_;
}
else
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 57;
v___x_327_ = lean_uint32_dec_le(v_c_309_, v___x_326_);
v___y_311_ = v___x_327_;
goto v___jp_310_;
}
}
else
{
return v___y_323_;
}
}
v___jp_328_:
{
uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 97;
v___x_330_ = lean_uint32_dec_le(v___x_329_, v_c_309_);
if (v___x_330_ == 0)
{
v___y_323_ = v___x_330_;
goto v___jp_322_;
}
else
{
uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = 122;
v___x_332_ = lean_uint32_dec_le(v_c_309_, v___x_331_);
v___y_323_ = v___x_332_;
goto v___jp_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_337_){
_start:
{
uint32_t v_c_boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_c_boxed_338_ = lean_unbox_uint32(v_c_337_);
lean_dec(v_c_337_);
v_res_339_ = l_Lean_isIdRest(v_c_boxed_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0(void){
_start:
{
uint32_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 39;
v___x_342_ = lean_uint32_to_uint8(v___x_341_);
return v___x_342_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1(void){
_start:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 33;
v___x_344_ = lean_uint32_to_uint8(v___x_343_);
return v___x_344_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2(void){
_start:
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 63;
v___x_346_ = lean_uint32_to_uint8(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_347_){
_start:
{
uint8_t v___y_349_; uint8_t v___y_359_; uint8_t v___y_365_; uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_371_ = lean_uint8_dec_le(v___x_370_, v_c_347_);
if (v___x_371_ == 0)
{
v___y_365_ = v___x_371_;
goto v___jp_364_;
}
else
{
uint8_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_373_ = lean_uint8_dec_le(v_c_347_, v___x_372_);
v___y_365_ = v___x_373_;
goto v___jp_364_;
}
v___jp_348_:
{
if (v___y_349_ == 0)
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_351_ = lean_uint8_dec_eq(v_c_347_, v___x_350_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_353_ = lean_uint8_dec_eq(v_c_347_, v___x_352_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_355_ = lean_uint8_dec_eq(v_c_347_, v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_357_ = lean_uint8_dec_eq(v_c_347_, v___x_356_);
return v___x_357_;
}
else
{
return v___x_355_;
}
}
else
{
return v___x_353_;
}
}
else
{
return v___x_351_;
}
}
else
{
return v___y_349_;
}
}
v___jp_358_:
{
if (v___y_359_ == 0)
{
uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_361_ = lean_uint8_dec_le(v___x_360_, v_c_347_);
if (v___x_361_ == 0)
{
v___y_349_ = v___x_361_;
goto v___jp_348_;
}
else
{
uint8_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_363_ = lean_uint8_dec_le(v_c_347_, v___x_362_);
v___y_349_ = v___x_363_;
goto v___jp_348_;
}
}
else
{
return v___y_359_;
}
}
v___jp_364_:
{
if (v___y_365_ == 0)
{
uint8_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_367_ = lean_uint8_dec_le(v___x_366_, v_c_347_);
if (v___x_367_ == 0)
{
v___y_359_ = v___x_367_;
goto v___jp_358_;
}
else
{
uint8_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_369_ = lean_uint8_dec_le(v_c_347_, v___x_368_);
v___y_359_ = v___x_369_;
goto v___jp_358_;
}
}
else
{
return v___y_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_374_){
_start:
{
uint8_t v_c_boxed_375_; uint8_t v_res_376_; lean_object* v_r_377_; 
v_c_boxed_375_ = lean_unbox(v_c_374_);
v_res_376_ = l_Lean_isIdRestAscii(v_c_boxed_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_378_; 
v___x_378_ = 171;
return v___x_378_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_379_; 
v___x_379_ = 187;
return v___x_379_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_380_){
_start:
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 171;
v___x_382_ = lean_uint32_dec_eq(v_c_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_383_){
_start:
{
uint32_t v_c_boxed_384_; uint8_t v_res_385_; lean_object* v_r_386_; 
v_c_boxed_384_ = lean_unbox_uint32(v_c_383_);
lean_dec(v_c_383_);
v_res_385_ = l_Lean_isIdBeginEscape(v_c_boxed_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_387_){
_start:
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 187;
v___x_389_ = lean_uint32_dec_eq(v_c_387_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_390_){
_start:
{
uint32_t v_c_boxed_391_; uint8_t v_res_392_; lean_object* v_r_393_; 
v_c_boxed_391_ = lean_unbox_uint32(v_c_390_);
lean_dec(v_c_390_);
v_res_392_ = l_Lean_isIdEndEscape(v_c_boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
return v_x_394_;
}
else
{
lean_object* v_pre_395_; 
v_pre_395_ = lean_ctor_get(v_x_394_, 0);
if (lean_obj_tag(v_pre_395_) == 0)
{
lean_inc(v_x_394_);
return v_x_394_;
}
else
{
v_x_394_ = v_pre_395_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Name_getRoot(v_x_397_);
lean_dec(v_x_397_);
return v_res_398_;
}
}
LEAN_EXPORT uint8_t lean_is_inaccessible_user_name(lean_object* v_x_400_){
_start:
{
switch(lean_obj_tag(v_x_400_))
{
case 1:
{
lean_object* v_str_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v_str_401_ = lean_ctor_get(v_x_400_, 1);
lean_inc_ref(v_str_401_);
lean_dec_ref(v_x_400_);
v___x_402_ = 10013;
lean_inc_ref(v_str_401_);
v___x_403_ = lean_string_contains(v_str_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_405_ = lean_string_dec_eq(v_str_401_, v___x_404_);
lean_dec_ref(v_str_401_);
return v___x_405_;
}
else
{
lean_dec_ref(v_str_401_);
return v___x_403_;
}
}
case 2:
{
lean_object* v_pre_406_; 
v_pre_406_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_pre_406_);
lean_dec_ref(v_x_400_);
v_x_400_ = v_pre_406_;
goto _start;
}
default: 
{
uint8_t v___x_408_; 
lean_dec(v_x_400_);
v___x_408_ = 0;
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = lean_is_inaccessible_user_name(v_x_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_412_, lean_object* v_i_413_){
_start:
{
uint8_t v___y_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_string_utf8_byte_size(v_s_412_);
v___x_421_ = lean_nat_dec_lt(v_i_413_, v___x_420_);
if (v___x_421_ == 0)
{
uint8_t v___x_422_; 
lean_dec(v_i_413_);
v___x_422_ = 1;
return v___x_422_;
}
else
{
uint8_t v_c_423_; uint8_t v___y_425_; uint8_t v___y_435_; uint8_t v___y_441_; uint8_t v___x_446_; uint8_t v___x_447_; 
lean_inc(v_i_413_);
v_c_423_ = lean_string_get_byte_fast(v_s_412_, v_i_413_);
v___x_446_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_447_ = lean_uint8_dec_le(v___x_446_, v_c_423_);
if (v___x_447_ == 0)
{
v___y_441_ = v___x_447_;
goto v___jp_440_;
}
else
{
uint8_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_449_ = lean_uint8_dec_le(v_c_423_, v___x_448_);
v___y_441_ = v___x_449_;
goto v___jp_440_;
}
v___jp_424_:
{
if (v___y_425_ == 0)
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_427_ = lean_uint8_dec_eq(v_c_423_, v___x_426_);
if (v___x_427_ == 0)
{
uint8_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_429_ = lean_uint8_dec_eq(v_c_423_, v___x_428_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_431_ = lean_uint8_dec_eq(v_c_423_, v___x_430_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_433_ = lean_uint8_dec_eq(v_c_423_, v___x_432_);
v___y_419_ = v___x_433_;
goto v___jp_418_;
}
else
{
v___y_419_ = v___x_431_;
goto v___jp_418_;
}
}
else
{
v___y_419_ = v___x_429_;
goto v___jp_418_;
}
}
else
{
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
}
else
{
goto v___jp_414_;
}
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_437_ = lean_uint8_dec_le(v___x_436_, v_c_423_);
if (v___x_437_ == 0)
{
v___y_425_ = v___x_437_;
goto v___jp_424_;
}
else
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_439_ = lean_uint8_dec_le(v_c_423_, v___x_438_);
v___y_425_ = v___x_439_;
goto v___jp_424_;
}
}
else
{
goto v___jp_414_;
}
}
v___jp_440_:
{
if (v___y_441_ == 0)
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_443_ = lean_uint8_dec_le(v___x_442_, v_c_423_);
if (v___x_443_ == 0)
{
v___y_435_ = v___x_443_;
goto v___jp_434_;
}
else
{
uint8_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_445_ = lean_uint8_dec_le(v_c_423_, v___x_444_);
v___y_435_ = v___x_445_;
goto v___jp_434_;
}
}
else
{
goto v___jp_414_;
}
}
}
v___jp_414_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_i_413_, v___x_415_);
lean_dec(v_i_413_);
v_i_413_ = v___x_416_;
goto _start;
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_dec(v_i_413_);
return v___y_419_;
}
else
{
goto v___jp_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_450_, lean_object* v_i_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_450_, v_i_451_);
lean_dec_ref(v_s_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_454_){
_start:
{
lean_object* v___x_458_; uint8_t v_c_459_; uint8_t v___y_461_; uint8_t v___y_465_; uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v_c_459_ = lean_string_get_byte_fast(v_s_454_, v___x_458_);
v___x_470_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_471_ = lean_uint8_dec_le(v___x_470_, v_c_459_);
if (v___x_471_ == 0)
{
v___y_465_ = v___x_471_;
goto v___jp_464_;
}
else
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_473_ = lean_uint8_dec_le(v_c_459_, v___x_472_);
v___y_465_ = v___x_473_;
goto v___jp_464_;
}
v___jp_455_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_454_, v___x_456_);
return v___x_457_;
}
v___jp_460_:
{
if (v___y_461_ == 0)
{
uint8_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_463_ = lean_uint8_dec_eq(v_c_459_, v___x_462_);
if (v___x_463_ == 0)
{
return v___x_463_;
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
v___jp_464_:
{
if (v___y_465_ == 0)
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_467_ = lean_uint8_dec_le(v___x_466_, v_c_459_);
if (v___x_467_ == 0)
{
v___y_461_ = v___x_467_;
goto v___jp_460_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_469_ = lean_uint8_dec_le(v_c_459_, v___x_468_);
v___y_461_ = v___x_469_;
goto v___jp_460_;
}
}
else
{
goto v___jp_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_474_);
lean_dec_ref(v_s_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_477_, lean_object* v_h_478_){
_start:
{
lean_object* v___x_482_; uint8_t v_c_483_; uint8_t v___y_485_; uint8_t v___y_489_; uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v_c_483_ = lean_string_get_byte_fast(v_s_477_, v___x_482_);
v___x_494_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_495_ = lean_uint8_dec_le(v___x_494_, v_c_483_);
if (v___x_495_ == 0)
{
v___y_489_ = v___x_495_;
goto v___jp_488_;
}
else
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_497_ = lean_uint8_dec_le(v_c_483_, v___x_496_);
v___y_489_ = v___x_497_;
goto v___jp_488_;
}
v___jp_479_:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_477_, v___x_480_);
return v___x_481_;
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_487_ = lean_uint8_dec_eq(v_c_483_, v___x_486_);
if (v___x_487_ == 0)
{
return v___x_487_;
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
v___jp_488_:
{
if (v___y_489_ == 0)
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_491_ = lean_uint8_dec_le(v___x_490_, v_c_483_);
if (v___x_491_ == 0)
{
v___y_485_ = v___x_491_;
goto v___jp_484_;
}
else
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_493_ = lean_uint8_dec_le(v_c_483_, v___x_492_);
v___y_485_ = v___x_493_;
goto v___jp_484_;
}
}
else
{
goto v___jp_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_498_, lean_object* v_h_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_498_, v_h_499_);
lean_dec_ref(v_s_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_503_){
_start:
{
uint8_t v___y_513_; uint32_t v___y_515_; uint8_t v___y_516_; uint32_t v___y_521_; uint8_t v___y_527_; lean_object* v___x_537_; uint8_t v_c_538_; uint8_t v___y_540_; uint8_t v___y_544_; uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v_c_538_ = lean_string_get_byte_fast(v_s_503_, v___x_537_);
v___x_549_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_550_ = lean_uint8_dec_le(v___x_549_, v_c_538_);
if (v___x_550_ == 0)
{
v___y_544_ = v___x_550_;
goto v___jp_543_;
}
else
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_552_ = lean_uint8_dec_le(v_c_538_, v___x_551_);
v___y_544_ = v___x_552_;
goto v___jp_543_;
}
v___jp_504_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_string_utf8_byte_size(v_s_503_);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_s_503_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_substring_drop(v___x_507_, v___x_508_);
v___x_510_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_511_ = lean_substring_all(v___x_509_, v___x_510_);
return v___x_511_;
}
v___jp_512_:
{
if (v___y_513_ == 0)
{
lean_dec_ref(v_s_503_);
return v___y_513_;
}
else
{
goto v___jp_504_;
}
}
v___jp_514_:
{
if (v___y_516_ == 0)
{
uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = 95;
v___x_518_ = lean_uint32_dec_eq(v___y_515_, v___x_517_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_isLetterLike(v___y_515_);
v___y_513_ = v___x_519_;
goto v___jp_512_;
}
else
{
v___y_513_ = v___x_518_;
goto v___jp_512_;
}
}
else
{
goto v___jp_504_;
}
}
v___jp_520_:
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 97;
v___x_523_ = lean_uint32_dec_le(v___x_522_, v___y_521_);
if (v___x_523_ == 0)
{
v___y_515_ = v___y_521_;
v___y_516_ = v___x_523_;
goto v___jp_514_;
}
else
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 122;
v___x_525_ = lean_uint32_dec_le(v___y_521_, v___x_524_);
v___y_515_ = v___y_521_;
v___y_516_ = v___x_525_;
goto v___jp_514_;
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_object* v___x_528_; uint32_t v___x_529_; uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_string_utf8_get(v_s_503_, v___x_528_);
v___x_530_ = 65;
v___x_531_ = lean_uint32_dec_le(v___x_530_, v___x_529_);
if (v___x_531_ == 0)
{
v___y_521_ = v___x_529_;
goto v___jp_520_;
}
else
{
uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = 90;
v___x_533_ = lean_uint32_dec_le(v___x_529_, v___x_532_);
if (v___x_533_ == 0)
{
v___y_521_ = v___x_529_;
goto v___jp_520_;
}
else
{
goto v___jp_504_;
}
}
}
else
{
lean_dec_ref(v_s_503_);
return v___y_527_;
}
}
v___jp_534_:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_503_, v___x_535_);
v___y_527_ = v___x_536_;
goto v___jp_526_;
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_542_ = lean_uint8_dec_eq(v_c_538_, v___x_541_);
if (v___x_542_ == 0)
{
v___y_527_ = v___x_542_;
goto v___jp_526_;
}
else
{
goto v___jp_534_;
}
}
else
{
goto v___jp_534_;
}
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_546_ = lean_uint8_dec_le(v___x_545_, v_c_538_);
if (v___x_546_ == 0)
{
v___y_540_ = v___x_546_;
goto v___jp_539_;
}
else
{
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_548_ = lean_uint8_dec_le(v_c_538_, v___x_547_);
v___y_540_ = v___x_548_;
goto v___jp_539_;
}
}
else
{
goto v___jp_534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_553_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_556_, lean_object* v_h_557_){
_start:
{
uint8_t v___y_567_; uint32_t v___y_569_; uint8_t v___y_570_; uint32_t v___y_575_; uint8_t v___y_581_; lean_object* v___x_591_; uint8_t v_c_592_; uint8_t v___y_594_; uint8_t v___y_598_; uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v_c_592_ = lean_string_get_byte_fast(v_s_556_, v___x_591_);
v___x_603_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_604_ = lean_uint8_dec_le(v___x_603_, v_c_592_);
if (v___x_604_ == 0)
{
v___y_598_ = v___x_604_;
goto v___jp_597_;
}
else
{
uint8_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_606_ = lean_uint8_dec_le(v_c_592_, v___x_605_);
v___y_598_ = v___x_606_;
goto v___jp_597_;
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_string_utf8_byte_size(v_s_556_);
v___x_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_561_, 0, v_s_556_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_substring_drop(v___x_561_, v___x_562_);
v___x_564_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_565_ = lean_substring_all(v___x_563_, v___x_564_);
return v___x_565_;
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
lean_dec_ref(v_s_556_);
return v___y_567_;
}
else
{
goto v___jp_558_;
}
}
v___jp_568_:
{
if (v___y_570_ == 0)
{
uint32_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 95;
v___x_572_ = lean_uint32_dec_eq(v___y_569_, v___x_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_isLetterLike(v___y_569_);
v___y_567_ = v___x_573_;
goto v___jp_566_;
}
else
{
v___y_567_ = v___x_572_;
goto v___jp_566_;
}
}
else
{
goto v___jp_558_;
}
}
v___jp_574_:
{
uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 97;
v___x_577_ = lean_uint32_dec_le(v___x_576_, v___y_575_);
if (v___x_577_ == 0)
{
v___y_569_ = v___y_575_;
v___y_570_ = v___x_577_;
goto v___jp_568_;
}
else
{
uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 122;
v___x_579_ = lean_uint32_dec_le(v___y_575_, v___x_578_);
v___y_569_ = v___y_575_;
v___y_570_ = v___x_579_;
goto v___jp_568_;
}
}
v___jp_580_:
{
if (v___y_581_ == 0)
{
lean_object* v___x_582_; uint32_t v___x_583_; uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_string_utf8_get(v_s_556_, v___x_582_);
v___x_584_ = 65;
v___x_585_ = lean_uint32_dec_le(v___x_584_, v___x_583_);
if (v___x_585_ == 0)
{
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
else
{
uint32_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = 90;
v___x_587_ = lean_uint32_dec_le(v___x_583_, v___x_586_);
if (v___x_587_ == 0)
{
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
else
{
goto v___jp_558_;
}
}
}
else
{
lean_dec_ref(v_s_556_);
return v___y_581_;
}
}
v___jp_588_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_556_, v___x_589_);
v___y_581_ = v___x_590_;
goto v___jp_580_;
}
v___jp_593_:
{
if (v___y_594_ == 0)
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_596_ = lean_uint8_dec_eq(v_c_592_, v___x_595_);
if (v___x_596_ == 0)
{
v___y_581_ = v___x_596_;
goto v___jp_580_;
}
else
{
goto v___jp_588_;
}
}
else
{
goto v___jp_588_;
}
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_600_ = lean_uint8_dec_le(v___x_599_, v_c_592_);
if (v___x_600_ == 0)
{
v___y_594_ = v___x_600_;
goto v___jp_593_;
}
else
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_602_ = lean_uint8_dec_le(v_c_592_, v___x_601_);
v___y_594_ = v___x_602_;
goto v___jp_593_;
}
}
else
{
goto v___jp_588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_607_, lean_object* v_h_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_607_, v_h_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0(void){
_start:
{
uint32_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = 171;
v___x_612_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_613_ = lean_string_push(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = 187;
v___x_615_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_616_ = lean_string_push(v___x_615_, v___x_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_618_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_619_ = lean_string_append(v___x_618_, v_s_617_);
v___x_620_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_621_ = lean_string_append(v___x_619_, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_622_);
lean_dec_ref(v_s_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_625_, uint8_t v_force_626_){
_start:
{
uint8_t v___y_646_; uint32_t v___y_648_; uint8_t v___y_649_; uint32_t v___y_654_; uint8_t v___y_660_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_string_utf8_byte_size(v_s_625_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_674_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_675_ = lean_string_append(v___x_674_, v_s_625_);
lean_dec_ref(v_s_625_);
v___x_676_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_677_ = lean_string_append(v___x_675_, v___x_676_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
else
{
if (v_force_626_ == 0)
{
uint8_t v_c_679_; uint8_t v___y_681_; uint8_t v___y_685_; uint8_t v___x_690_; uint8_t v___x_691_; 
v_c_679_ = lean_string_get_byte_fast(v_s_625_, v___x_671_);
v___x_690_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_691_ = lean_uint8_dec_le(v___x_690_, v_c_679_);
if (v___x_691_ == 0)
{
v___y_685_ = v___x_691_;
goto v___jp_684_;
}
else
{
uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_693_ = lean_uint8_dec_le(v_c_679_, v___x_692_);
v___y_685_ = v___x_693_;
goto v___jp_684_;
}
v___jp_680_:
{
if (v___y_681_ == 0)
{
uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_683_ = lean_uint8_dec_eq(v_c_679_, v___x_682_);
if (v___x_683_ == 0)
{
v___y_660_ = v___x_683_;
goto v___jp_659_;
}
else
{
goto v___jp_668_;
}
}
else
{
goto v___jp_668_;
}
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
uint8_t v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_687_ = lean_uint8_dec_le(v___x_686_, v_c_679_);
if (v___x_687_ == 0)
{
v___y_681_ = v___x_687_;
goto v___jp_680_;
}
else
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_689_ = lean_uint8_dec_le(v_c_679_, v___x_688_);
v___y_681_ = v___x_689_;
goto v___jp_680_;
}
}
else
{
goto v___jp_668_;
}
}
}
else
{
goto v___jp_627_;
}
}
v___jp_627_:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_625_);
v___x_629_ = lean_string_any(v_s_625_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_631_ = lean_string_append(v___x_630_, v_s_625_);
lean_dec_ref(v_s_625_);
v___x_632_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_633_ = lean_string_append(v___x_631_, v___x_632_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_s_625_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
v___jp_636_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_string_utf8_byte_size(v_s_625_);
lean_inc_ref(v_s_625_);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v_s_625_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_substring_drop(v___x_639_, v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_643_ = lean_substring_all(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
goto v___jp_627_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_s_625_);
return v___x_644_;
}
}
v___jp_645_:
{
if (v___y_646_ == 0)
{
goto v___jp_627_;
}
else
{
goto v___jp_636_;
}
}
v___jp_647_:
{
if (v___y_649_ == 0)
{
uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 95;
v___x_651_ = lean_uint32_dec_eq(v___y_648_, v___x_650_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; 
v___x_652_ = l_Lean_isLetterLike(v___y_648_);
v___y_646_ = v___x_652_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___x_651_;
goto v___jp_645_;
}
}
else
{
goto v___jp_636_;
}
}
v___jp_653_:
{
uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 97;
v___x_656_ = lean_uint32_dec_le(v___x_655_, v___y_654_);
if (v___x_656_ == 0)
{
v___y_648_ = v___y_654_;
v___y_649_ = v___x_656_;
goto v___jp_647_;
}
else
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 122;
v___x_658_ = lean_uint32_dec_le(v___y_654_, v___x_657_);
v___y_648_ = v___y_654_;
v___y_649_ = v___x_658_;
goto v___jp_647_;
}
}
v___jp_659_:
{
if (v___y_660_ == 0)
{
lean_object* v___x_661_; uint32_t v___x_662_; uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_string_utf8_get(v_s_625_, v___x_661_);
v___x_663_ = 65;
v___x_664_ = lean_uint32_dec_le(v___x_663_, v___x_662_);
if (v___x_664_ == 0)
{
v___y_654_ = v___x_662_;
goto v___jp_653_;
}
else
{
uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 90;
v___x_666_ = lean_uint32_dec_le(v___x_662_, v___x_665_);
if (v___x_666_ == 0)
{
v___y_654_ = v___x_662_;
goto v___jp_653_;
}
else
{
goto v___jp_636_;
}
}
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_s_625_);
return v___x_667_;
}
}
v___jp_668_:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_625_, v___x_669_);
v___y_660_ = v___x_670_;
goto v___jp_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_694_, lean_object* v_force_695_){
_start:
{
uint8_t v_force_boxed_696_; lean_object* v_res_697_; 
v_force_boxed_696_ = lean_unbox(v_force_695_);
v_res_697_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_694_, v_force_boxed_696_);
return v_res_697_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_698_){
_start:
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 187;
v___x_700_ = lean_uint32_dec_eq(v___y_698_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_701_){
_start:
{
uint32_t v___y_435__boxed_702_; uint8_t v_res_703_; lean_object* v_r_704_; 
v___y_435__boxed_702_ = lean_unbox_uint32(v___y_701_);
lean_dec(v___y_701_);
v_res_703_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_435__boxed_702_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_705_){
_start:
{
uint8_t v___y_707_; uint8_t v___y_719_; uint32_t v___x_729_; uint8_t v___x_730_; 
v___x_729_ = 65;
v___x_730_ = lean_uint32_dec_le(v___x_729_, v___y_705_);
if (v___x_730_ == 0)
{
goto v___jp_724_;
}
else
{
uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 90;
v___x_732_ = lean_uint32_dec_le(v___y_705_, v___x_731_);
if (v___x_732_ == 0)
{
goto v___jp_724_;
}
else
{
return v___x_732_;
}
}
v___jp_706_:
{
if (v___y_707_ == 0)
{
uint32_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 95;
v___x_709_ = lean_uint32_dec_eq(v___y_705_, v___x_708_);
if (v___x_709_ == 0)
{
uint32_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = 39;
v___x_711_ = lean_uint32_dec_eq(v___y_705_, v___x_710_);
if (v___x_711_ == 0)
{
uint32_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = 33;
v___x_713_ = lean_uint32_dec_eq(v___y_705_, v___x_712_);
if (v___x_713_ == 0)
{
uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 63;
v___x_715_ = lean_uint32_dec_eq(v___y_705_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_isLetterLike(v___y_705_);
if (v___x_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_isSubScriptAlnum(v___y_705_);
return v___x_717_;
}
else
{
return v___x_716_;
}
}
else
{
return v___x_715_;
}
}
else
{
return v___x_713_;
}
}
else
{
return v___x_711_;
}
}
else
{
return v___x_709_;
}
}
else
{
return v___y_707_;
}
}
v___jp_718_:
{
if (v___y_719_ == 0)
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 48;
v___x_721_ = lean_uint32_dec_le(v___x_720_, v___y_705_);
if (v___x_721_ == 0)
{
v___y_707_ = v___x_721_;
goto v___jp_706_;
}
else
{
uint32_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 57;
v___x_723_ = lean_uint32_dec_le(v___y_705_, v___x_722_);
v___y_707_ = v___x_723_;
goto v___jp_706_;
}
}
else
{
return v___y_719_;
}
}
v___jp_724_:
{
uint32_t v___x_725_; uint8_t v___x_726_; 
v___x_725_ = 97;
v___x_726_ = lean_uint32_dec_le(v___x_725_, v___y_705_);
if (v___x_726_ == 0)
{
v___y_719_ = v___x_726_;
goto v___jp_718_;
}
else
{
uint32_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 122;
v___x_728_ = lean_uint32_dec_le(v___y_705_, v___x_727_);
v___y_719_ = v___x_728_;
goto v___jp_718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_733_){
_start:
{
uint32_t v___y_442__boxed_734_; uint8_t v_res_735_; lean_object* v_r_736_; 
v___y_442__boxed_734_ = lean_unbox_uint32(v___y_733_);
lean_dec(v___y_733_);
v_res_735_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_442__boxed_734_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_739_, lean_object* v_s_740_, uint8_t v_force_741_){
_start:
{
if (v_escape_739_ == 0)
{
return v_s_740_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_string_utf8_byte_size(v_s_740_);
v___x_744_ = lean_nat_dec_lt(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_745_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_746_ = lean_string_append(v___x_745_, v_s_740_);
lean_dec_ref(v_s_740_);
v___x_747_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_748_ = lean_string_append(v___x_746_, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v___f_749_; 
v___f_749_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_741_ == 0)
{
lean_object* v___f_756_; uint8_t v___y_763_; uint32_t v___y_765_; uint8_t v___y_766_; uint32_t v___y_771_; uint8_t v___y_777_; uint8_t v_c_786_; uint8_t v___y_788_; uint8_t v___y_792_; uint8_t v___x_797_; uint8_t v___x_798_; 
v___f_756_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_786_ = lean_string_get_byte_fast(v_s_740_, v___x_742_);
v___x_797_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_798_ = lean_uint8_dec_le(v___x_797_, v_c_786_);
if (v___x_798_ == 0)
{
v___y_792_ = v___x_798_;
goto v___jp_791_;
}
else
{
uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_800_ = lean_uint8_dec_le(v_c_786_, v___x_799_);
v___y_792_ = v___x_800_;
goto v___jp_791_;
}
v___jp_757_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
lean_inc_ref(v_s_740_);
v___x_758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_758_, 0, v_s_740_);
lean_ctor_set(v___x_758_, 1, v___x_742_);
lean_ctor_set(v___x_758_, 2, v___x_743_);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_substring_drop(v___x_758_, v___x_759_);
v___x_761_ = lean_substring_all(v___x_760_, v___f_756_);
if (v___x_761_ == 0)
{
goto v___jp_750_;
}
else
{
return v_s_740_;
}
}
v___jp_762_:
{
if (v___y_763_ == 0)
{
goto v___jp_750_;
}
else
{
goto v___jp_757_;
}
}
v___jp_764_:
{
if (v___y_766_ == 0)
{
uint32_t v___x_767_; uint8_t v___x_768_; 
v___x_767_ = 95;
v___x_768_ = lean_uint32_dec_eq(v___y_765_, v___x_767_);
if (v___x_768_ == 0)
{
uint8_t v___x_769_; 
v___x_769_ = l_Lean_isLetterLike(v___y_765_);
v___y_763_ = v___x_769_;
goto v___jp_762_;
}
else
{
v___y_763_ = v___x_768_;
goto v___jp_762_;
}
}
else
{
goto v___jp_757_;
}
}
v___jp_770_:
{
uint32_t v___x_772_; uint8_t v___x_773_; 
v___x_772_ = 97;
v___x_773_ = lean_uint32_dec_le(v___x_772_, v___y_771_);
if (v___x_773_ == 0)
{
v___y_765_ = v___y_771_;
v___y_766_ = v___x_773_;
goto v___jp_764_;
}
else
{
uint32_t v___x_774_; uint8_t v___x_775_; 
v___x_774_ = 122;
v___x_775_ = lean_uint32_dec_le(v___y_771_, v___x_774_);
v___y_765_ = v___y_771_;
v___y_766_ = v___x_775_;
goto v___jp_764_;
}
}
v___jp_776_:
{
if (v___y_777_ == 0)
{
uint32_t v___x_778_; uint32_t v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_string_utf8_get(v_s_740_, v___x_742_);
v___x_779_ = 65;
v___x_780_ = lean_uint32_dec_le(v___x_779_, v___x_778_);
if (v___x_780_ == 0)
{
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
else
{
uint32_t v___x_781_; uint8_t v___x_782_; 
v___x_781_ = 90;
v___x_782_ = lean_uint32_dec_le(v___x_778_, v___x_781_);
if (v___x_782_ == 0)
{
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
else
{
goto v___jp_757_;
}
}
}
else
{
return v_s_740_;
}
}
v___jp_783_:
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_740_, v___x_784_);
v___y_777_ = v___x_785_;
goto v___jp_776_;
}
v___jp_787_:
{
if (v___y_788_ == 0)
{
uint8_t v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_790_ = lean_uint8_dec_eq(v_c_786_, v___x_789_);
if (v___x_790_ == 0)
{
v___y_777_ = v___x_790_;
goto v___jp_776_;
}
else
{
goto v___jp_783_;
}
}
else
{
goto v___jp_783_;
}
}
v___jp_791_:
{
if (v___y_792_ == 0)
{
uint8_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_794_ = lean_uint8_dec_le(v___x_793_, v_c_786_);
if (v___x_794_ == 0)
{
v___y_788_ = v___x_794_;
goto v___jp_787_;
}
else
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_796_ = lean_uint8_dec_le(v_c_786_, v___x_795_);
v___y_788_ = v___x_796_;
goto v___jp_787_;
}
}
else
{
goto v___jp_783_;
}
}
}
else
{
goto v___jp_750_;
}
v___jp_750_:
{
uint8_t v___x_751_; 
lean_inc_ref(v_s_740_);
v___x_751_ = lean_string_any(v_s_740_, v___f_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_753_ = lean_string_append(v___x_752_, v_s_740_);
lean_dec_ref(v_s_740_);
v___x_754_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_755_ = lean_string_append(v___x_753_, v___x_754_);
return v___x_755_;
}
else
{
return v_s_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_801_, lean_object* v_s_802_, lean_object* v_force_803_){
_start:
{
uint8_t v_escape_boxed_804_; uint8_t v_force_boxed_805_; lean_object* v_res_806_; 
v_escape_boxed_804_ = lean_unbox(v_escape_801_);
v_force_boxed_805_ = lean_unbox(v_force_803_);
v_res_806_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_804_, v_s_802_, v_force_boxed_805_);
return v_res_806_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_807_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_809_);
lean_dec_ref(v_x_809_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_814_, uint8_t v_escape_815_, lean_object* v_n_816_, lean_object* v_isToken_817_){
_start:
{
switch(lean_obj_tag(v_n_816_))
{
case 0:
{
lean_object* v___x_818_; 
lean_dec_ref(v_isToken_817_);
v___x_818_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_818_;
}
case 1:
{
lean_object* v_pre_819_; 
v_pre_819_ = lean_ctor_get(v_n_816_, 0);
if (lean_obj_tag(v_pre_819_) == 0)
{
lean_object* v_str_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v_str_820_ = lean_ctor_get(v_n_816_, 1);
lean_inc_ref(v_str_820_);
lean_dec_ref(v_n_816_);
lean_inc_ref(v_str_820_);
v___x_821_ = lean_apply_1(v_isToken_817_, v_str_820_);
v___x_822_ = lean_unbox(v___x_821_);
v___x_823_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_815_, v_str_820_, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_str_824_; lean_object* v_r_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v_r_x27_829_; 
lean_inc(v_pre_819_);
v_str_824_ = lean_ctor_get(v_n_816_, 1);
lean_inc_ref(v_str_824_);
lean_dec_ref(v_n_816_);
lean_inc_ref(v_isToken_817_);
v_r_825_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_814_, v_escape_815_, v_pre_819_, v_isToken_817_);
v___x_826_ = lean_string_append(v_r_825_, v_sep_814_);
v___x_827_ = 0;
lean_inc_ref(v_str_824_);
v___x_828_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_815_, v_str_824_, v___x_827_);
lean_inc_ref(v___x_826_);
v_r_x27_829_ = lean_string_append(v___x_826_, v___x_828_);
lean_dec_ref(v___x_828_);
if (v_escape_815_ == 0)
{
lean_dec_ref(v___x_826_);
lean_dec_ref(v_str_824_);
lean_dec_ref(v_isToken_817_);
return v_r_x27_829_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
lean_inc_ref(v_r_x27_829_);
v___x_830_ = lean_apply_1(v_isToken_817_, v_r_x27_829_);
v___x_831_ = lean_unbox(v___x_830_);
if (v___x_831_ == 0)
{
lean_dec_ref(v___x_826_);
lean_dec_ref(v_str_824_);
return v_r_x27_829_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v_r_x27_829_);
v___x_832_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_815_, v_str_824_, v_escape_815_);
v___x_833_ = lean_string_append(v___x_826_, v___x_832_);
lean_dec_ref(v___x_832_);
return v___x_833_;
}
}
}
}
default: 
{
lean_object* v_pre_834_; 
lean_dec_ref(v_isToken_817_);
v_pre_834_ = lean_ctor_get(v_n_816_, 0);
if (lean_obj_tag(v_pre_834_) == 0)
{
lean_object* v_i_835_; lean_object* v___x_836_; 
v_i_835_ = lean_ctor_get(v_n_816_, 1);
lean_inc(v_i_835_);
lean_dec_ref(v_n_816_);
v___x_836_ = l_Nat_reprFast(v_i_835_);
return v___x_836_;
}
else
{
lean_object* v_i_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc(v_pre_834_);
v_i_837_ = lean_ctor_get(v_n_816_, 1);
lean_inc(v_i_837_);
lean_dec_ref(v_n_816_);
v___f_838_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_839_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_814_, v_escape_815_, v_pre_834_, v___f_838_);
v___x_840_ = lean_string_append(v___x_839_, v_sep_814_);
v___x_841_ = l_Nat_reprFast(v_i_837_);
v___x_842_ = lean_string_append(v___x_840_, v___x_841_);
lean_dec_ref(v___x_841_);
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_843_, lean_object* v_escape_844_, lean_object* v_n_845_, lean_object* v_isToken_846_){
_start:
{
uint8_t v_escape_boxed_847_; lean_object* v_res_848_; 
v_escape_boxed_847_ = lean_unbox(v_escape_844_);
v_res_848_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_843_, v_escape_boxed_847_, v_n_845_, v_isToken_846_);
lean_dec_ref(v_sep_843_);
return v_res_848_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_854_){
_start:
{
lean_object* v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; 
v___x_855_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_856_ = lean_name_eq(v_n_854_, v___x_855_);
v___x_857_ = 1;
if (v___x_856_ == 0)
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Name_getRoot(v_n_854_);
if (lean_obj_tag(v___x_858_) == 1)
{
lean_object* v_str_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_str_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc_ref(v_str_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
lean_inc_ref(v_str_859_);
v___x_861_ = lean_string_isprefixof(v___x_860_, v_str_859_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_863_ = lean_string_isprefixof(v___x_862_, v_str_859_);
return v___x_863_;
}
else
{
lean_dec_ref(v_str_859_);
return v___x_857_;
}
}
else
{
lean_dec(v___x_858_);
return v___x_856_;
}
}
else
{
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_864_);
lean_dec(v_n_864_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_867_, uint8_t v_escape_868_, lean_object* v_isToken_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_868_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_870_, v_escape_868_, v_n_867_, v_isToken_869_);
return v___x_871_;
}
else
{
uint8_t v___x_872_; 
lean_inc(v_n_867_);
v___x_872_ = lean_is_inaccessible_user_name(v_n_867_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Name_hasMacroScopes(v_n_867_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_867_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_870_, v_escape_868_, v_n_867_, v_isToken_869_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_870_, v___x_873_, v_n_867_, v_isToken_869_);
return v___x_876_;
}
}
else
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_870_, v___x_872_, v_n_867_, v_isToken_869_);
return v___x_877_;
}
}
else
{
uint8_t v___x_878_; lean_object* v___x_879_; 
v___x_878_ = 0;
v___x_879_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_870_, v___x_878_, v_n_867_, v_isToken_869_);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_880_, lean_object* v_escape_881_, lean_object* v_isToken_882_){
_start:
{
uint8_t v_escape_boxed_883_; lean_object* v_res_884_; 
v_escape_boxed_883_ = lean_unbox(v_escape_881_);
v_res_884_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_880_, v_escape_boxed_883_, v_isToken_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_885_, uint8_t v_escape_886_, lean_object* v_n_887_){
_start:
{
switch(lean_obj_tag(v_n_887_))
{
case 0:
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_888_;
}
case 1:
{
lean_object* v_pre_889_; 
v_pre_889_ = lean_ctor_get(v_n_887_, 0);
if (lean_obj_tag(v_pre_889_) == 0)
{
lean_object* v_str_890_; uint8_t v___x_891_; lean_object* v___x_892_; 
v_str_890_ = lean_ctor_get(v_n_887_, 1);
lean_inc_ref(v_str_890_);
lean_dec_ref(v_n_887_);
v___x_891_ = 0;
v___x_892_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_886_, v_str_890_, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v_str_893_; lean_object* v_r_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v_r_x27_898_; 
lean_inc(v_pre_889_);
v_str_893_ = lean_ctor_get(v_n_887_, 1);
lean_inc_ref(v_str_893_);
lean_dec_ref(v_n_887_);
v_r_894_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_885_, v_escape_886_, v_pre_889_);
v___x_895_ = lean_string_append(v_r_894_, v_sep_885_);
v___x_896_ = 0;
v___x_897_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_886_, v_str_893_, v___x_896_);
v_r_x27_898_ = lean_string_append(v___x_895_, v___x_897_);
lean_dec_ref(v___x_897_);
return v_r_x27_898_;
}
}
default: 
{
lean_object* v_pre_899_; 
v_pre_899_ = lean_ctor_get(v_n_887_, 0);
if (lean_obj_tag(v_pre_899_) == 0)
{
lean_object* v_i_900_; lean_object* v___x_901_; 
v_i_900_ = lean_ctor_get(v_n_887_, 1);
lean_inc(v_i_900_);
lean_dec_ref(v_n_887_);
v___x_901_ = l_Nat_reprFast(v_i_900_);
return v___x_901_;
}
else
{
lean_object* v_i_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v_pre_899_);
v_i_902_ = lean_ctor_get(v_n_887_, 1);
lean_inc(v_i_902_);
lean_dec_ref(v_n_887_);
v___x_903_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_885_, v_escape_886_, v_pre_899_);
v___x_904_ = lean_string_append(v___x_903_, v_sep_885_);
v___x_905_ = l_Nat_reprFast(v_i_902_);
v___x_906_ = lean_string_append(v___x_904_, v___x_905_);
lean_dec_ref(v___x_905_);
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_907_, lean_object* v_escape_908_, lean_object* v_n_909_){
_start:
{
uint8_t v_escape_boxed_910_; lean_object* v_res_911_; 
v_escape_boxed_910_ = lean_unbox(v_escape_908_);
v_res_911_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_907_, v_escape_boxed_910_, v_n_909_);
lean_dec_ref(v_sep_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_912_, uint8_t v_escape_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_913_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_914_, v_escape_913_, v_n_912_);
return v___x_915_;
}
else
{
uint8_t v___x_916_; 
lean_inc(v_n_912_);
v___x_916_ = lean_is_inaccessible_user_name(v_n_912_);
if (v___x_916_ == 0)
{
uint8_t v___x_917_; 
v___x_917_ = l_Lean_Name_hasMacroScopes(v_n_912_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; 
v___x_918_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_912_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_914_, v_escape_913_, v_n_912_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_914_, v___x_917_, v_n_912_);
return v___x_920_;
}
}
else
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_914_, v___x_916_, v_n_912_);
return v___x_921_;
}
}
else
{
uint8_t v___x_922_; lean_object* v___x_923_; 
v___x_922_ = 0;
v___x_923_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_914_, v___x_922_, v_n_912_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_924_, lean_object* v_escape_925_){
_start:
{
uint8_t v_escape_boxed_926_; lean_object* v_res_927_; 
v_escape_boxed_926_ = lean_unbox(v_escape_925_);
v_res_927_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_924_, v_escape_boxed_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_928_, uint8_t v_escape_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_928_, v_escape_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_931_, lean_object* v_escape_932_){
_start:
{
uint8_t v_escape_boxed_933_; lean_object* v_res_934_; 
v_escape_boxed_933_ = lean_unbox(v_escape_932_);
v_res_934_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_931_, v_escape_boxed_933_);
return v_res_934_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_935_){
_start:
{
switch(lean_obj_tag(v_x_935_))
{
case 0:
{
uint8_t v___x_936_; 
v___x_936_ = 0;
return v___x_936_;
}
case 1:
{
lean_object* v_pre_937_; 
v_pre_937_ = lean_ctor_get(v_x_935_, 0);
v_x_935_ = v_pre_937_;
goto _start;
}
default: 
{
uint8_t v___x_939_; 
v___x_939_ = 1;
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_940_);
lean_dec(v_x_940_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_958_, lean_object* v_prec_959_){
_start:
{
switch(lean_obj_tag(v_n_958_))
{
case 0:
{
lean_object* v___x_960_; 
v___x_960_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_960_;
}
case 1:
{
lean_object* v_pre_961_; lean_object* v_str_962_; uint8_t v___x_963_; 
v_pre_961_ = lean_ctor_get(v_n_958_, 0);
v_str_962_ = lean_ctor_get(v_n_958_, 1);
v___x_963_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_961_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_964_ = 1;
v___x_965_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_966_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_958_, v___x_964_);
v___x_967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc_ref(v_str_962_);
lean_inc(v_pre_961_);
lean_dec_ref(v_n_958_);
v___x_969_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_970_ = lean_unsigned_to_nat(1024u);
v___x_971_ = l_Lean_Name_reprPrec(v_pre_961_, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_969_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_String_quote(v_str_962_);
v___x_976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_974_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Repr_addAppParen(v___x_977_, v_prec_959_);
return v___x_978_;
}
}
default: 
{
lean_object* v_pre_979_; lean_object* v_i_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_pre_979_ = lean_ctor_get(v_n_958_, 0);
lean_inc(v_pre_979_);
v_i_980_ = lean_ctor_get(v_n_958_, 1);
lean_inc(v_i_980_);
lean_dec_ref(v_n_958_);
v___x_981_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_982_ = lean_unsigned_to_nat(1024u);
v___x_983_ = l_Lean_Name_reprPrec(v_pre_979_, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_981_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Nat_reprFast(v_i_980_);
v___x_988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_986_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Repr_addAppParen(v___x_989_, v_prec_959_);
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_991_, lean_object* v_prec_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Name_reprPrec(v_n_991_, v_prec_992_);
lean_dec(v_prec_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_996_) == 1)
{
lean_object* v_pre_997_; lean_object* v_str_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_pre_997_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_pre_997_);
v_str_998_ = lean_ctor_get(v_x_996_, 1);
lean_inc_ref(v_str_998_);
lean_dec_ref(v_x_996_);
v___x_999_ = lean_string_capitalize(v_str_998_);
v___x_1000_ = l_Lean_Name_str___override(v_pre_997_, v___x_999_);
return v___x_1000_;
}
else
{
return v_x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
switch(lean_obj_tag(v_x_1001_))
{
case 0:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_inc(v_x_1003_);
return v_x_1003_;
}
else
{
return v_x_1001_;
}
}
case 1:
{
lean_object* v_pre_1004_; lean_object* v_str_1005_; uint8_t v___x_1006_; 
v_pre_1004_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_pre_1004_);
v_str_1005_ = lean_ctor_get(v_x_1001_, 1);
lean_inc_ref(v_str_1005_);
v___x_1006_ = lean_name_eq(v_x_1001_, v_x_1002_);
lean_dec_ref(v_x_1001_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = l_Lean_Name_replacePrefix(v_pre_1004_, v_x_1002_, v_x_1003_);
v___x_1008_ = l_Lean_Name_str___override(v___x_1007_, v_str_1005_);
return v___x_1008_;
}
else
{
lean_dec_ref(v_str_1005_);
lean_dec(v_pre_1004_);
lean_inc(v_x_1003_);
return v_x_1003_;
}
}
default: 
{
lean_object* v_pre_1009_; lean_object* v_i_1010_; uint8_t v___x_1011_; 
v_pre_1009_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_pre_1009_);
v_i_1010_ = lean_ctor_get(v_x_1001_, 1);
lean_inc(v_i_1010_);
v___x_1011_ = lean_name_eq(v_x_1001_, v_x_1002_);
lean_dec_ref(v_x_1001_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = l_Lean_Name_replacePrefix(v_pre_1009_, v_x_1002_, v_x_1003_);
v___x_1013_ = l_Lean_Name_num___override(v___x_1012_, v_i_1010_);
return v___x_1013_;
}
else
{
lean_dec(v_i_1010_);
lean_dec(v_pre_1009_);
lean_inc(v_x_1003_);
return v_x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Name_replacePrefix(v_x_1014_, v_x_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec(v_x_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
switch(lean_obj_tag(v_x_1019_))
{
case 0:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_x_1018_);
return v___x_1020_;
}
case 1:
{
if (lean_obj_tag(v_x_1018_) == 1)
{
lean_object* v_pre_1021_; lean_object* v_str_1022_; lean_object* v_pre_1023_; lean_object* v_str_1024_; uint8_t v___x_1025_; 
v_pre_1021_ = lean_ctor_get(v_x_1019_, 0);
v_str_1022_ = lean_ctor_get(v_x_1019_, 1);
v_pre_1023_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_pre_1023_);
v_str_1024_ = lean_ctor_get(v_x_1018_, 1);
lean_inc_ref(v_str_1024_);
lean_dec_ref(v_x_1018_);
v___x_1025_ = lean_string_dec_eq(v_str_1024_, v_str_1022_);
lean_dec_ref(v_str_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_dec(v_pre_1023_);
v___x_1026_ = lean_box(0);
return v___x_1026_;
}
else
{
v_x_1018_ = v_pre_1023_;
v_x_1019_ = v_pre_1021_;
goto _start;
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_x_1018_);
v___x_1028_ = lean_box(0);
return v___x_1028_;
}
}
default: 
{
if (lean_obj_tag(v_x_1018_) == 2)
{
lean_object* v_pre_1029_; lean_object* v_i_1030_; lean_object* v_pre_1031_; lean_object* v_i_1032_; uint8_t v___x_1033_; 
v_pre_1029_ = lean_ctor_get(v_x_1019_, 0);
v_i_1030_ = lean_ctor_get(v_x_1019_, 1);
v_pre_1031_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_pre_1031_);
v_i_1032_ = lean_ctor_get(v_x_1018_, 1);
lean_inc(v_i_1032_);
lean_dec_ref(v_x_1018_);
v___x_1033_ = lean_nat_dec_eq(v_i_1032_, v_i_1030_);
lean_dec(v_i_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec(v_pre_1031_);
v___x_1034_ = lean_box(0);
return v___x_1034_;
}
else
{
v_x_1018_ = v_pre_1031_;
v_x_1019_ = v_pre_1029_;
goto _start;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_x_1018_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Name_eraseSuffix_x3f(v_x_1037_, v_x_1038_);
lean_dec(v_x_1038_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_1040_, lean_object* v_f_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Lean_Name_hasMacroScopes(v_n_1040_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_apply_1(v_f_1041_, v_n_1040_);
return v___x_1043_;
}
else
{
lean_object* v_view_1044_; lean_object* v_name_1045_; lean_object* v_imported_1046_; lean_object* v_ctx_1047_; lean_object* v_scopes_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1057_; 
v_view_1044_ = l_Lean_extractMacroScopes(v_n_1040_);
v_name_1045_ = lean_ctor_get(v_view_1044_, 0);
v_imported_1046_ = lean_ctor_get(v_view_1044_, 1);
v_ctx_1047_ = lean_ctor_get(v_view_1044_, 2);
v_scopes_1048_ = lean_ctor_get(v_view_1044_, 3);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_view_1044_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1050_ = v_view_1044_;
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_scopes_1048_);
lean_inc(v_ctx_1047_);
lean_inc(v_imported_1046_);
lean_inc(v_name_1045_);
lean_dec(v_view_1044_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_apply_1(v_f_1041_, v_name_1045_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_imported_1046_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_ctx_1047_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_scopes_1048_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_MacroScopesView_review(v___x_1054_);
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1058_, lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 1)
{
lean_object* v_pre_1060_; lean_object* v_str_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_pre_1060_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_pre_1060_);
v_str_1061_ = lean_ctor_get(v_x_1059_, 1);
lean_inc_ref(v_str_1061_);
lean_dec_ref(v_x_1059_);
v___x_1062_ = lean_string_append(v_str_1061_, v_suffix_1058_);
lean_dec_ref(v_suffix_1058_);
v___x_1063_ = l_Lean_Name_str___override(v_pre_1060_, v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Name_str___override(v_x_1059_, v_suffix_1058_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1065_, lean_object* v_suffix_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Lean_Name_hasMacroScopes(v_n_1065_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1066_, v_n_1065_);
return v___x_1068_;
}
else
{
lean_object* v_view_1069_; lean_object* v_name_1070_; lean_object* v_imported_1071_; lean_object* v_ctx_1072_; lean_object* v_scopes_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1082_; 
v_view_1069_ = l_Lean_extractMacroScopes(v_n_1065_);
v_name_1070_ = lean_ctor_get(v_view_1069_, 0);
v_imported_1071_ = lean_ctor_get(v_view_1069_, 1);
v_ctx_1072_ = lean_ctor_get(v_view_1069_, 2);
v_scopes_1073_ = lean_ctor_get(v_view_1069_, 3);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_view_1069_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1075_ = v_view_1069_;
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_scopes_1073_);
lean_inc(v_ctx_1072_);
lean_inc(v_imported_1071_);
lean_inc(v_name_1070_);
lean_dec(v_view_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1066_, v_name_1070_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_imported_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_ctx_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_scopes_1073_);
v___x_1079_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_MacroScopesView_review(v___x_1079_);
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1083_, lean_object* v_x_1084_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 1)
{
lean_object* v_pre_1085_; lean_object* v_str_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_pre_1085_ = lean_ctor_get(v_x_1084_, 0);
lean_inc(v_pre_1085_);
v_str_1086_ = lean_ctor_get(v_x_1084_, 1);
lean_inc_ref(v_str_1086_);
lean_dec_ref(v_x_1084_);
v___x_1087_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1088_ = lean_string_append(v_str_1086_, v___x_1087_);
v___x_1089_ = l_Nat_reprFast(v_idx_1083_);
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = l_Lean_Name_str___override(v_pre_1085_, v___x_1090_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1093_ = l_Nat_reprFast(v_idx_1083_);
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l_Lean_Name_str___override(v_x_1084_, v___x_1094_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1096_, lean_object* v_idx_1097_){
_start:
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Name_hasMacroScopes(v_n_1096_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1097_, v_n_1096_);
return v___x_1099_;
}
else
{
lean_object* v_view_1100_; lean_object* v_name_1101_; lean_object* v_imported_1102_; lean_object* v_ctx_1103_; lean_object* v_scopes_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1113_; 
v_view_1100_ = l_Lean_extractMacroScopes(v_n_1096_);
v_name_1101_ = lean_ctor_get(v_view_1100_, 0);
v_imported_1102_ = lean_ctor_get(v_view_1100_, 1);
v_ctx_1103_ = lean_ctor_get(v_view_1100_, 2);
v_scopes_1104_ = lean_ctor_get(v_view_1100_, 3);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_view_1100_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1106_ = v_view_1100_;
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_scopes_1104_);
lean_inc(v_ctx_1103_);
lean_inc(v_imported_1102_);
lean_inc(v_name_1101_);
lean_dec(v_view_1100_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1097_, v_name_1101_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_imported_1102_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_ctx_1103_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_scopes_1104_);
v___x_1110_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_MacroScopesView_review(v___x_1110_);
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1114_, lean_object* v_x_1115_){
_start:
{
switch(lean_obj_tag(v_x_1115_))
{
case 0:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Name_str___override(v_x_1115_, v_pre_1114_);
return v___x_1116_;
}
case 1:
{
lean_object* v_pre_1117_; lean_object* v_str_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_pre_1117_ = lean_ctor_get(v_x_1115_, 0);
lean_inc(v_pre_1117_);
v_str_1118_ = lean_ctor_get(v_x_1115_, 1);
lean_inc_ref(v_str_1118_);
lean_dec_ref(v_x_1115_);
v___x_1119_ = lean_string_append(v_pre_1114_, v_str_1118_);
lean_dec_ref(v_str_1118_);
v___x_1120_ = l_Lean_Name_str___override(v_pre_1117_, v___x_1119_);
return v___x_1120_;
}
default: 
{
lean_object* v_pre_1121_; lean_object* v_i_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_pre_1121_ = lean_ctor_get(v_x_1115_, 0);
lean_inc(v_pre_1121_);
v_i_1122_ = lean_ctor_get(v_x_1115_, 1);
lean_inc(v_i_1122_);
lean_dec_ref(v_x_1115_);
v___x_1123_ = l_Lean_Name_str___override(v_pre_1121_, v_pre_1114_);
v___x_1124_ = l_Lean_Name_num___override(v___x_1123_, v_i_1122_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_append_before(lean_object* v_n_1125_, lean_object* v_pre_1126_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_Name_hasMacroScopes(v_n_1125_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Name_appendBefore___lam__0(v_pre_1126_, v_n_1125_);
return v___x_1128_;
}
else
{
lean_object* v_view_1129_; lean_object* v_name_1130_; lean_object* v_imported_1131_; lean_object* v_ctx_1132_; lean_object* v_scopes_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1142_; 
v_view_1129_ = l_Lean_extractMacroScopes(v_n_1125_);
v_name_1130_ = lean_ctor_get(v_view_1129_, 0);
v_imported_1131_ = lean_ctor_get(v_view_1129_, 1);
v_ctx_1132_ = lean_ctor_get(v_view_1129_, 2);
v_scopes_1133_ = lean_ctor_get(v_view_1129_, 3);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_view_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1135_ = v_view_1129_;
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_scopes_1133_);
lean_inc(v_ctx_1132_);
lean_inc(v_imported_1131_);
lean_inc(v_name_1130_);
lean_dec(v_view_1129_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_Name_appendBefore___lam__0(v_pre_1126_, v_name_1130_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_imported_1131_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_ctx_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_scopes_1133_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_MacroScopesView_review(v___x_1139_);
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_h__1_1145_, lean_object* v_h__2_1146_, lean_object* v_h__3_1147_, lean_object* v_h__4_1148_){
_start:
{
switch(lean_obj_tag(v_x_1143_))
{
case 0:
{
lean_dec(v_h__3_1147_);
lean_dec(v_h__2_1146_);
if (lean_obj_tag(v_x_1144_) == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_h__4_1148_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_apply_1(v_h__1_1145_, v___x_1149_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; 
lean_dec(v_h__1_1145_);
v___x_1151_ = lean_apply_5(v_h__4_1148_, v_x_1143_, v_x_1144_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1151_;
}
}
case 1:
{
lean_dec(v_h__3_1147_);
lean_dec(v_h__1_1145_);
if (lean_obj_tag(v_x_1144_) == 1)
{
lean_object* v_pre_1152_; lean_object* v_str_1153_; lean_object* v_pre_1154_; lean_object* v_str_1155_; lean_object* v___x_1156_; 
lean_dec(v_h__4_1148_);
v_pre_1152_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_pre_1152_);
v_str_1153_ = lean_ctor_get(v_x_1143_, 1);
lean_inc_ref(v_str_1153_);
lean_dec_ref(v_x_1143_);
v_pre_1154_ = lean_ctor_get(v_x_1144_, 0);
lean_inc(v_pre_1154_);
v_str_1155_ = lean_ctor_get(v_x_1144_, 1);
lean_inc_ref(v_str_1155_);
lean_dec_ref(v_x_1144_);
v___x_1156_ = lean_apply_4(v_h__2_1146_, v_pre_1152_, v_str_1153_, v_pre_1154_, v_str_1155_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_h__2_1146_);
v___x_1157_ = lean_apply_5(v_h__4_1148_, v_x_1143_, v_x_1144_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1157_;
}
}
default: 
{
lean_dec(v_h__2_1146_);
lean_dec(v_h__1_1145_);
if (lean_obj_tag(v_x_1144_) == 2)
{
lean_object* v_pre_1158_; lean_object* v_i_1159_; lean_object* v_pre_1160_; lean_object* v_i_1161_; lean_object* v___x_1162_; 
lean_dec(v_h__4_1148_);
v_pre_1158_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_pre_1158_);
v_i_1159_ = lean_ctor_get(v_x_1143_, 1);
lean_inc(v_i_1159_);
lean_dec_ref(v_x_1143_);
v_pre_1160_ = lean_ctor_get(v_x_1144_, 0);
lean_inc(v_pre_1160_);
v_i_1161_ = lean_ctor_get(v_x_1144_, 1);
lean_inc(v_i_1161_);
lean_dec_ref(v_x_1144_);
v___x_1162_ = lean_apply_4(v_h__3_1147_, v_pre_1158_, v_i_1159_, v_pre_1160_, v_i_1161_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; 
lean_dec(v_h__3_1147_);
v___x_1163_ = lean_apply_5(v_h__4_1148_, v_x_1143_, v_x_1144_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_h__1_1167_, lean_object* v_h__2_1168_, lean_object* v_h__3_1169_, lean_object* v_h__4_1170_){
_start:
{
switch(lean_obj_tag(v_x_1165_))
{
case 0:
{
lean_dec(v_h__3_1169_);
lean_dec(v_h__2_1168_);
if (lean_obj_tag(v_x_1166_) == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v_h__4_1170_);
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_apply_1(v_h__1_1167_, v___x_1171_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec(v_h__1_1167_);
v___x_1173_ = lean_apply_5(v_h__4_1170_, v_x_1165_, v_x_1166_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1173_;
}
}
case 1:
{
lean_dec(v_h__3_1169_);
lean_dec(v_h__1_1167_);
if (lean_obj_tag(v_x_1166_) == 1)
{
lean_object* v_pre_1174_; lean_object* v_str_1175_; lean_object* v_pre_1176_; lean_object* v_str_1177_; lean_object* v___x_1178_; 
lean_dec(v_h__4_1170_);
v_pre_1174_ = lean_ctor_get(v_x_1165_, 0);
lean_inc(v_pre_1174_);
v_str_1175_ = lean_ctor_get(v_x_1165_, 1);
lean_inc_ref(v_str_1175_);
lean_dec_ref(v_x_1165_);
v_pre_1176_ = lean_ctor_get(v_x_1166_, 0);
lean_inc(v_pre_1176_);
v_str_1177_ = lean_ctor_get(v_x_1166_, 1);
lean_inc_ref(v_str_1177_);
lean_dec_ref(v_x_1166_);
v___x_1178_ = lean_apply_4(v_h__2_1168_, v_pre_1174_, v_str_1175_, v_pre_1176_, v_str_1177_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; 
lean_dec(v_h__2_1168_);
v___x_1179_ = lean_apply_5(v_h__4_1170_, v_x_1165_, v_x_1166_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1179_;
}
}
default: 
{
lean_dec(v_h__2_1168_);
lean_dec(v_h__1_1167_);
if (lean_obj_tag(v_x_1166_) == 2)
{
lean_object* v_pre_1180_; lean_object* v_i_1181_; lean_object* v_pre_1182_; lean_object* v_i_1183_; lean_object* v___x_1184_; 
lean_dec(v_h__4_1170_);
v_pre_1180_ = lean_ctor_get(v_x_1165_, 0);
lean_inc(v_pre_1180_);
v_i_1181_ = lean_ctor_get(v_x_1165_, 1);
lean_inc(v_i_1181_);
lean_dec_ref(v_x_1165_);
v_pre_1182_ = lean_ctor_get(v_x_1166_, 0);
lean_inc(v_pre_1182_);
v_i_1183_ = lean_ctor_get(v_x_1166_, 1);
lean_inc(v_i_1183_);
lean_dec_ref(v_x_1166_);
v___x_1184_ = lean_apply_4(v_h__3_1169_, v_pre_1180_, v_i_1181_, v_pre_1182_, v_i_1183_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_h__3_1169_);
v___x_1185_ = lean_apply_5(v_h__4_1170_, v_x_1165_, v_x_1166_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1186_, lean_object* v_b_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_name_eq(v_a_1186_, v_b_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1189_, lean_object* v_b_1190_){
_start:
{
uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_res_1191_ = l_Lean_Name_instDecidableEq(v_a_1189_, v_b_1190_);
lean_dec(v_b_1190_);
lean_dec(v_a_1189_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1193_){
_start:
{
lean_object* v_namePrefix_1194_; lean_object* v_idx_1195_; lean_object* v___x_1196_; 
v_namePrefix_1194_ = lean_ctor_get(v_g_1193_, 0);
lean_inc(v_namePrefix_1194_);
v_idx_1195_ = lean_ctor_get(v_g_1193_, 1);
lean_inc(v_idx_1195_);
lean_dec_ref(v_g_1193_);
v___x_1196_ = l_Lean_Name_num___override(v_namePrefix_1194_, v_idx_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1197_){
_start:
{
lean_object* v_namePrefix_1198_; lean_object* v_idx_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_namePrefix_1198_ = lean_ctor_get(v_g_1197_, 0);
v_idx_1199_ = lean_ctor_get(v_g_1197_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_g_1197_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v_g_1197_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_idx_1199_);
lean_inc(v_namePrefix_1198_);
lean_dec(v_g_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = lean_nat_add(v_idx_1199_, v___x_1203_);
lean_dec(v_idx_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_namePrefix_1198_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1209_){
_start:
{
lean_object* v_namePrefix_1210_; lean_object* v_idx_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1223_; 
v_namePrefix_1210_ = lean_ctor_get(v_g_1209_, 0);
v_idx_1211_ = lean_ctor_get(v_g_1209_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_g_1209_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1213_ = v_g_1209_;
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_idx_1211_);
lean_inc(v_namePrefix_1210_);
lean_dec(v_g_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
lean_inc(v_idx_1211_);
lean_inc(v_namePrefix_1210_);
v___x_1215_ = l_Lean_Name_num___override(v_namePrefix_1210_, v_idx_1211_);
v___x_1216_ = lean_unsigned_to_nat(1u);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v___x_1216_);
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1218_ = v___x_1213_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_nat_add(v_idx_1211_, v___x_1216_);
lean_dec(v_idx_1211_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_namePrefix_1210_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1218_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1224_, lean_object* v_r_1225_, lean_object* v_____r_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_apply_2(v_toPure_1224_, lean_box(0), v_r_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1228_, lean_object* v_setNGen_1229_, lean_object* v_toBind_1230_, lean_object* v_ngen_1231_){
_start:
{
lean_object* v_namePrefix_1232_; lean_object* v_idx_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1246_; 
v_namePrefix_1232_ = lean_ctor_get(v_ngen_1231_, 0);
v_idx_1233_ = lean_ctor_get(v_ngen_1231_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_ngen_1231_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1235_ = v_ngen_1231_;
v_isShared_1236_ = v_isSharedCheck_1246_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_idx_1233_);
lean_inc(v_namePrefix_1232_);
lean_dec(v_ngen_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1246_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_r_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_inc(v_idx_1233_);
lean_inc(v_namePrefix_1232_);
v_r_1237_ = l_Lean_Name_num___override(v_namePrefix_1232_, v_idx_1233_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1238_, 0, v_toPure_1228_);
lean_closure_set(v___f_1238_, 1, v_r_1237_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_idx_1233_, v___x_1239_);
lean_dec(v_idx_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1240_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_namePrefix_1232_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_apply_1(v_setNGen_1229_, v___x_1242_);
v___x_1244_ = lean_apply_4(v_toBind_1230_, lean_box(0), lean_box(0), v___x_1243_, v___f_1238_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1247_, lean_object* v_inst_1248_){
_start:
{
lean_object* v_toApplicative_1249_; lean_object* v_toBind_1250_; lean_object* v_getNGen_1251_; lean_object* v_setNGen_1252_; lean_object* v_toPure_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; 
v_toApplicative_1249_ = lean_ctor_get(v_inst_1247_, 0);
lean_inc_ref(v_toApplicative_1249_);
v_toBind_1250_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc(v_toBind_1250_);
lean_dec_ref(v_inst_1247_);
v_getNGen_1251_ = lean_ctor_get(v_inst_1248_, 0);
lean_inc(v_getNGen_1251_);
v_setNGen_1252_ = lean_ctor_get(v_inst_1248_, 1);
lean_inc(v_setNGen_1252_);
lean_dec_ref(v_inst_1248_);
v_toPure_1253_ = lean_ctor_get(v_toApplicative_1249_, 1);
lean_inc(v_toPure_1253_);
lean_dec_ref(v_toApplicative_1249_);
lean_inc(v_toBind_1250_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1254_, 0, v_toPure_1253_);
lean_closure_set(v___f_1254_, 1, v_setNGen_1252_);
lean_closure_set(v___f_1254_, 2, v_toBind_1250_);
v___x_1255_ = lean_apply_4(v_toBind_1250_, lean_box(0), lean_box(0), v_getNGen_1251_, v___f_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_mkFreshId___redArg(v_inst_1257_, v_inst_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1260_, lean_object* v_inst_1261_, lean_object* v_ngen_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_apply_1(v_setNGen_1260_, v_ngen_1262_);
v___x_1264_ = lean_apply_2(v_inst_1261_, lean_box(0), v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1265_, lean_object* v_inst_1266_){
_start:
{
lean_object* v_getNGen_1267_; lean_object* v_setNGen_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1277_; 
v_getNGen_1267_ = lean_ctor_get(v_inst_1266_, 0);
v_setNGen_1268_ = lean_ctor_get(v_inst_1266_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_inst_1266_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1270_ = v_inst_1266_;
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_setNGen_1268_);
lean_inc(v_getNGen_1267_);
lean_dec(v_inst_1266_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_inc(v_inst_1265_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1272_, 0, v_setNGen_1268_);
lean_closure_set(v___f_1272_, 1, v_inst_1265_);
v___x_1273_ = lean_apply_2(v_inst_1265_, lean_box(0), v_getNGen_1267_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___f_1272_);
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___f_1272_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1278_, lean_object* v_n_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1280_, v_inst_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
lean_dec(v_x_1283_);
return v_x_1284_;
}
else
{
lean_object* v_head_1286_; lean_object* v_tail_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1298_; 
v_head_1286_ = lean_ctor_get(v_x_1285_, 0);
v_tail_1287_ = lean_ctor_get(v_x_1285_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_x_1285_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1289_ = v_x_1285_;
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_tail_1287_);
lean_inc(v_head_1286_);
lean_dec(v_x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
lean_inc(v_x_1283_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 5);
lean_ctor_set(v___x_1289_, 1, v_x_1283_);
lean_ctor_set(v___x_1289_, 0, v_x_1284_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_x_1284_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_x_1283_);
v___x_1292_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = l_String_quote(v_head_1286_);
v___x_1294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1292_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v_x_1284_ = v___x_1295_;
v_x_1285_ = v_tail_1287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 0)
{
lean_dec(v_x_1299_);
return v_x_1300_;
}
else
{
lean_object* v_head_1302_; lean_object* v_tail_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1314_; 
v_head_1302_ = lean_ctor_get(v_x_1301_, 0);
v_tail_1303_ = lean_ctor_get(v_x_1301_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1305_ = v_x_1301_;
v_isShared_1306_ = v_isSharedCheck_1314_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_tail_1303_);
lean_inc(v_head_1302_);
lean_dec(v_x_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1314_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
lean_inc(v_x_1299_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 5);
lean_ctor_set(v___x_1305_, 1, v_x_1299_);
lean_ctor_set(v___x_1305_, 0, v_x_1300_);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_x_1300_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_x_1299_);
v___x_1308_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = l_String_quote(v_head_1302_);
v___x_1310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1308_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1299_, v___x_1311_, v_tail_1303_);
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = l_String_quote(v___y_1315_);
v___x_1317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_x_1319_);
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v_tail_1321_; 
v_tail_1321_ = lean_ctor_get(v_x_1318_, 1);
if (lean_obj_tag(v_tail_1321_) == 0)
{
lean_object* v_head_1322_; lean_object* v___x_1323_; 
lean_dec(v_x_1319_);
v_head_1322_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_head_1322_);
lean_dec_ref(v_x_1318_);
v___x_1323_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1322_);
return v___x_1323_;
}
else
{
lean_object* v_head_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_inc(v_tail_1321_);
v_head_1324_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_head_1324_);
lean_dec_ref(v_x_1318_);
v___x_1325_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1324_);
v___x_1326_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1319_, v___x_1325_, v_tail_1321_);
return v___x_1326_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1339_ = lean_string_length(v___x_1338_);
return v___x_1339_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1341_ = lean_nat_to_int(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1346_){
_start:
{
if (lean_obj_tag(v_a_1346_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1348_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1349_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1346_, v___x_1348_);
v___x_1350_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1351_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1349_);
v___x_1353_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1350_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Std_Format_fill(v___x_1355_);
return v___x_1356_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(2u);
v___x_1364_ = lean_nat_to_int(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_to_int(v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1373_, lean_object* v_prec_1374_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
lean_object* v_ns_1375_; lean_object* v___y_1377_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_ns_1375_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_ns_1375_);
lean_dec_ref(v_x_1373_);
v___x_1386_ = lean_unsigned_to_nat(1024u);
v___x_1387_ = lean_nat_dec_le(v___x_1386_, v_prec_1374_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1377_ = v___x_1388_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1377_ = v___x_1389_;
goto v___jp_1376_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1378_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1379_ = lean_unsigned_to_nat(1024u);
v___x_1380_ = l_Lean_Name_reprPrec(v_ns_1375_, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1378_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___y_1377_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = 0;
v___x_1384_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*1, v___x_1383_);
v___x_1385_ = l_Repr_addAppParen(v___x_1384_, v_prec_1374_);
return v___x_1385_;
}
}
else
{
lean_object* v_n_1390_; lean_object* v_fields_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1415_; 
v_n_1390_ = lean_ctor_get(v_x_1373_, 0);
v_fields_1391_ = lean_ctor_get(v_x_1373_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1373_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1393_ = v_x_1373_;
v_isShared_1394_ = v_isSharedCheck_1415_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_fields_1391_);
lean_inc(v_n_1390_);
lean_dec(v_x_1373_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1415_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___y_1396_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_unsigned_to_nat(1024u);
v___x_1412_ = lean_nat_dec_le(v___x_1411_, v_prec_1374_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1396_ = v___x_1413_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1396_ = v___x_1414_;
goto v___jp_1395_;
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1397_ = lean_box(1);
v___x_1398_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1399_ = lean_unsigned_to_nat(1024u);
v___x_1400_ = l_Lean_Name_reprPrec(v_n_1390_, v___x_1399_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 5);
lean_ctor_set(v___x_1393_, 1, v___x_1400_);
lean_ctor_set(v___x_1393_, 0, v___x_1398_);
v___x_1402_ = v___x_1393_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v___x_1397_);
v___x_1404_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1391_);
v___x_1405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___y_1396_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = 0;
v___x_1408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*1, v___x_1407_);
v___x_1409_ = l_Repr_addAppParen(v___x_1408_, v_prec_1374_);
return v___x_1409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1416_, lean_object* v_prec_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1416_, v_prec_1417_);
lean_dec(v_prec_1417_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_nat_to_int(v_a_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1421_, lean_object* v_n_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1424_, lean_object* v_n_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1424_, v_n_1425_);
lean_dec(v_n_1425_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1429_, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_dec(v_x_1432_);
return v_x_1433_;
}
else
{
lean_object* v_head_1435_; lean_object* v_tail_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1447_; 
v_head_1435_ = lean_ctor_get(v_x_1434_, 0);
v_tail_1436_ = lean_ctor_get(v_x_1434_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1438_ = v_x_1434_;
v_isShared_1439_ = v_isSharedCheck_1447_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_tail_1436_);
lean_inc(v_head_1435_);
lean_dec(v_x_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1447_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
lean_inc(v_x_1432_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 5);
lean_ctor_set(v___x_1438_, 1, v_x_1432_);
lean_ctor_set(v___x_1438_, 0, v_x_1433_);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_x_1433_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_x_1432_);
v___x_1441_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1435_, v___x_1442_);
v___x_1444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1441_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v_x_1433_ = v___x_1444_;
v_x_1434_ = v_tail_1436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
lean_dec(v_x_1448_);
return v_x_1449_;
}
else
{
lean_object* v_head_1451_; lean_object* v_tail_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1463_; 
v_head_1451_ = lean_ctor_get(v_x_1450_, 0);
v_tail_1452_ = lean_ctor_get(v_x_1450_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1454_ = v_x_1450_;
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_tail_1452_);
lean_inc(v_head_1451_);
lean_dec(v_x_1450_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
lean_inc(v_x_1448_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 5);
lean_ctor_set(v___x_1454_, 1, v_x_1448_);
lean_ctor_set(v___x_1454_, 0, v_x_1449_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_x_1449_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_x_1448_);
v___x_1457_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1451_, v___x_1458_);
v___x_1460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1448_, v___x_1460_, v_tail_1452_);
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
if (lean_obj_tag(v_x_1464_) == 0)
{
lean_object* v___x_1466_; 
lean_dec(v_x_1465_);
v___x_1466_ = lean_box(0);
return v___x_1466_;
}
else
{
lean_object* v_tail_1467_; 
v_tail_1467_ = lean_ctor_get(v_x_1464_, 1);
if (lean_obj_tag(v_tail_1467_) == 0)
{
lean_object* v_head_1468_; lean_object* v___x_1469_; 
lean_dec(v_x_1465_);
v_head_1468_ = lean_ctor_get(v_x_1464_, 0);
lean_inc(v_head_1468_);
lean_dec_ref(v_x_1464_);
v___x_1469_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1468_);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v_tail_1467_);
v_head_1470_ = lean_ctor_get(v_x_1464_, 0);
lean_inc(v_head_1470_);
lean_dec_ref(v_x_1464_);
v___x_1471_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1470_);
v___x_1472_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1465_, v___x_1471_, v_tail_1467_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1473_){
_start:
{
if (lean_obj_tag(v_a_1473_) == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1475_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1476_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1473_, v___x_1475_);
v___x_1477_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1478_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1476_);
v___x_1480_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1477_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = 0;
v___x_1484_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*1, v___x_1483_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 0)
{
lean_dec(v_x_1494_);
return v_x_1495_;
}
else
{
lean_object* v_head_1497_; lean_object* v_tail_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1509_; 
v_head_1497_ = lean_ctor_get(v_x_1496_, 0);
v_tail_1498_ = lean_ctor_get(v_x_1496_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_x_1496_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1500_ = v_x_1496_;
v_isShared_1501_ = v_isSharedCheck_1509_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_tail_1498_);
lean_inc(v_head_1497_);
lean_dec(v_x_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1509_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
lean_inc(v_x_1494_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 5);
lean_ctor_set(v___x_1500_, 1, v_x_1494_);
lean_ctor_set(v___x_1500_, 0, v_x_1495_);
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_x_1495_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_x_1494_);
v___x_1503_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = l_Lean_Syntax_instRepr_repr(v_head_1497_, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1503_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v_x_1495_ = v___x_1506_;
v_x_1496_ = v_tail_1498_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 0)
{
lean_dec(v_x_1510_);
return v_x_1511_;
}
else
{
lean_object* v_head_1513_; lean_object* v_tail_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1525_; 
v_head_1513_ = lean_ctor_get(v_x_1512_, 0);
v_tail_1514_ = lean_ctor_get(v_x_1512_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_x_1512_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1516_ = v_x_1512_;
v_isShared_1517_ = v_isSharedCheck_1525_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_tail_1514_);
lean_inc(v_head_1513_);
lean_dec(v_x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1525_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
lean_inc(v_x_1510_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 5);
lean_ctor_set(v___x_1516_, 1, v_x_1510_);
lean_ctor_set(v___x_1516_, 0, v_x_1511_);
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_x_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_x_1510_);
v___x_1519_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = l_Lean_Syntax_instRepr_repr(v_head_1513_, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1510_, v___x_1522_, v_tail_1514_);
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1526_) == 0)
{
lean_object* v___x_1528_; 
lean_dec(v_x_1527_);
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
else
{
lean_object* v_tail_1529_; 
v_tail_1529_ = lean_ctor_get(v_x_1526_, 1);
if (lean_obj_tag(v_tail_1529_) == 0)
{
lean_object* v_head_1530_; lean_object* v___x_1531_; 
lean_dec(v_x_1527_);
v_head_1530_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_head_1530_);
lean_dec_ref(v_x_1526_);
v___x_1531_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1530_);
return v___x_1531_;
}
else
{
lean_object* v_head_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_inc(v_tail_1529_);
v_head_1532_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_head_1532_);
lean_dec_ref(v_x_1526_);
v___x_1533_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1532_);
v___x_1534_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1527_, v___x_1533_, v_tail_1529_);
return v___x_1534_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1537_ = lean_string_length(v___x_1536_);
return v___x_1537_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1539_ = lean_nat_to_int(v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_array_get_size(v_xs_1545_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1549_ = lean_array_to_list(v_xs_1545_);
v___x_1550_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1551_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1549_, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1553_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1551_);
v___x_1555_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1552_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Std_Format_fill(v___x_1557_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; 
lean_dec_ref(v_xs_1545_);
v___x_1559_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1573_, lean_object* v_prec_1574_){
_start:
{
lean_object* v___y_1576_; 
switch(lean_obj_tag(v_x_1573_))
{
case 0:
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_unsigned_to_nat(1024u);
v___x_1583_ = lean_nat_dec_le(v___x_1582_, v_prec_1574_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1576_ = v___x_1584_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1576_ = v___x_1585_;
goto v___jp_1575_;
}
}
case 1:
{
lean_object* v_info_1586_; lean_object* v_kind_1587_; lean_object* v_args_1588_; lean_object* v___y_1590_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_info_1586_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_info_1586_);
v_kind_1587_ = lean_ctor_get(v_x_1573_, 1);
lean_inc(v_kind_1587_);
v_args_1588_ = lean_ctor_get(v_x_1573_, 2);
lean_inc_ref(v_args_1588_);
lean_dec_ref(v_x_1573_);
v___x_1606_ = lean_unsigned_to_nat(1024u);
v___x_1607_ = lean_nat_dec_le(v___x_1606_, v_prec_1574_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1590_ = v___x_1608_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1590_ = v___x_1609_;
goto v___jp_1589_;
}
v___jp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1591_ = lean_box(1);
v___x_1592_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1593_ = lean_unsigned_to_nat(1024u);
v___x_1594_ = l_instReprSourceInfo_repr(v_info_1586_, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1592_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___x_1591_);
v___x_1597_ = l_Lean_Name_reprPrec(v_kind_1587_, v___x_1593_);
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___x_1591_);
v___x_1600_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1588_);
v___x_1601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___y_1590_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = 0;
v___x_1604_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*1, v___x_1603_);
v___x_1605_ = l_Repr_addAppParen(v___x_1604_, v_prec_1574_);
return v___x_1605_;
}
}
case 2:
{
lean_object* v_info_1610_; lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1636_; 
v_info_1610_ = lean_ctor_get(v_x_1573_, 0);
v_val_1611_ = lean_ctor_get(v_x_1573_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_x_1573_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1613_ = v_x_1573_;
v_isShared_1614_ = v_isSharedCheck_1636_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_inc(v_info_1610_);
lean_dec(v_x_1573_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1636_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___y_1616_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = lean_unsigned_to_nat(1024u);
v___x_1633_ = lean_nat_dec_le(v___x_1632_, v_prec_1574_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1616_ = v___x_1634_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1616_ = v___x_1635_;
goto v___jp_1615_;
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1617_ = lean_box(1);
v___x_1618_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1619_ = lean_unsigned_to_nat(1024u);
v___x_1620_ = l_instReprSourceInfo_repr(v_info_1610_, v___x_1619_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 5);
lean_ctor_set(v___x_1613_, 1, v___x_1620_);
lean_ctor_set(v___x_1613_, 0, v___x_1618_);
v___x_1622_ = v___x_1613_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___x_1617_);
v___x_1624_ = l_String_quote(v_val_1611_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1623_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1616_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = 0;
v___x_1629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*1, v___x_1628_);
v___x_1630_ = l_Repr_addAppParen(v___x_1629_, v_prec_1574_);
return v___x_1630_;
}
}
}
}
default: 
{
lean_object* v_info_1637_; lean_object* v_rawVal_1638_; lean_object* v_val_1639_; lean_object* v_preresolved_1640_; lean_object* v___y_1642_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_info_1637_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_info_1637_);
v_rawVal_1638_ = lean_ctor_get(v_x_1573_, 1);
lean_inc_ref(v_rawVal_1638_);
v_val_1639_ = lean_ctor_get(v_x_1573_, 2);
lean_inc(v_val_1639_);
v_preresolved_1640_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_preresolved_1640_);
lean_dec_ref(v_x_1573_);
v___x_1665_ = lean_unsigned_to_nat(1024u);
v___x_1666_ = lean_nat_dec_le(v___x_1665_, v_prec_1574_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1642_ = v___x_1667_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1642_ = v___x_1668_;
goto v___jp_1641_;
}
v___jp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1643_ = lean_box(1);
v___x_1644_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1645_ = lean_unsigned_to_nat(1024u);
v___x_1646_ = l_instReprSourceInfo_repr(v_info_1637_, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1644_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1643_);
v___x_1649_ = lean_substring_tostring(v_rawVal_1638_);
v___x_1650_ = l_String_quote(v___x_1649_);
v___x_1651_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1652_ = lean_string_append(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1648_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1643_);
v___x_1656_ = l_Lean_Name_reprPrec(v_val_1639_, v___x_1645_);
v___x_1657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1643_);
v___x_1659_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1640_);
v___x_1660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1642_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = 0;
v___x_1663_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*1, v___x_1662_);
v___x_1664_ = l_Repr_addAppParen(v___x_1663_, v_prec_1574_);
return v___x_1664_;
}
}
}
v___jp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1577_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
v___x_1581_ = l_Repr_addAppParen(v___x_1580_, v_prec_1574_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = l_Lean_Syntax_instRepr_repr(v___y_1669_, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1672_, lean_object* v_prec_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Syntax_instRepr_repr(v_x_1672_, v_prec_1673_);
lean_dec(v_prec_1673_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1675_, lean_object* v_n_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1678_, lean_object* v_n_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1678_, v_n_1679_);
lean_dec(v_n_1679_);
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(7u);
v___x_1697_ = lean_nat_to_int(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1700_ = lean_string_length(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1702_ = lean_nat_to_int(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1708_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1709_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = l_Lean_Syntax_instRepr_repr(v_x_1707_, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1709_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = 0;
v___x_1714_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*1, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1708_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1717_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v___x_1715_);
v___x_1719_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*1, v___x_1713_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1723_, lean_object* v_x_1724_, lean_object* v_prec_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1727_, lean_object* v_x_1728_, lean_object* v_prec_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1727_, v_x_1728_, v_prec_1729_);
lean_dec(v_prec_1729_);
lean_dec(v_ks_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1732_, 0, v_ks_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object* v_stx_1733_){
_start:
{
lean_inc(v_stx_1733_);
return v_stx_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object* v_stx_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(v_stx_1734_);
lean_dec(v_stx_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1737_, lean_object* v_ks_1738_){
_start:
{
lean_object* v___f_1739_; 
v___f_1739_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0));
return v___f_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1740_, lean_object* v_ks_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1740_, v_ks_1741_);
lean_dec(v_ks_1741_);
lean_dec(v_k_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1743_, lean_object* v_k_x27_1744_){
_start:
{
lean_object* v___f_1745_; 
v___f_1745_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0));
return v___f_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1746_, lean_object* v_k_x27_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1746_, v_k_x27_1747_);
lean_dec(v_k_x27_1747_);
lean_dec(v_ks_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1749_){
_start:
{
lean_inc(v_s_1749_);
return v_s_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1750_);
lean_dec(v_s_1750_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1754_, lean_object* v_ss_1755_, lean_object* v_n_1756_, lean_object* v_res_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1758_, 0, v_info_1754_);
lean_ctor_set(v___x_1758_, 1, v_ss_1755_);
lean_ctor_set(v___x_1758_, 2, v_n_1756_);
lean_ctor_set(v___x_1758_, 3, v_res_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1767_){
_start:
{
lean_object* v___f_1768_; 
v___f_1768_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1769_);
lean_dec(v_k_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1772_, 0, v_k_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1773_) == 0)
{
if (lean_obj_tag(v_x_1774_) == 0)
{
uint8_t v___x_1775_; 
v___x_1775_ = 1;
return v___x_1775_;
}
else
{
uint8_t v___x_1776_; 
v___x_1776_ = 0;
return v___x_1776_;
}
}
else
{
if (lean_obj_tag(v_x_1774_) == 0)
{
uint8_t v___x_1777_; 
v___x_1777_ = 0;
return v___x_1777_;
}
else
{
lean_object* v_head_1778_; lean_object* v_tail_1779_; lean_object* v_head_1780_; lean_object* v_tail_1781_; uint8_t v___x_1782_; 
v_head_1778_ = lean_ctor_get(v_x_1773_, 0);
v_tail_1779_ = lean_ctor_get(v_x_1773_, 1);
v_head_1780_ = lean_ctor_get(v_x_1774_, 0);
v_tail_1781_ = lean_ctor_get(v_x_1774_, 1);
v___x_1782_ = lean_string_dec_eq(v_head_1778_, v_head_1780_);
if (v___x_1782_ == 0)
{
return v___x_1782_;
}
else
{
v_x_1773_ = v_tail_1779_;
v_x_1774_ = v_tail_1781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
uint8_t v_res_1786_; lean_object* v_r_1787_; 
v_res_1786_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1784_, v_x_1785_);
lean_dec(v_x_1785_);
lean_dec(v_x_1784_);
v_r_1787_ = lean_box(v_res_1786_);
return v_r_1787_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 0)
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v_ns_1790_; lean_object* v_ns_1791_; uint8_t v___x_1792_; 
v_ns_1790_ = lean_ctor_get(v_x_1788_, 0);
v_ns_1791_ = lean_ctor_get(v_x_1789_, 0);
v___x_1792_ = lean_name_eq(v_ns_1790_, v_ns_1791_);
return v___x_1792_;
}
else
{
uint8_t v___x_1793_; 
v___x_1793_ = 0;
return v___x_1793_;
}
}
else
{
if (lean_obj_tag(v_x_1789_) == 1)
{
lean_object* v_n_1794_; lean_object* v_fields_1795_; lean_object* v_n_1796_; lean_object* v_fields_1797_; uint8_t v___x_1798_; 
v_n_1794_ = lean_ctor_get(v_x_1788_, 0);
v_fields_1795_ = lean_ctor_get(v_x_1788_, 1);
v_n_1796_ = lean_ctor_get(v_x_1789_, 0);
v_fields_1797_ = lean_ctor_get(v_x_1789_, 1);
v___x_1798_ = lean_name_eq(v_n_1794_, v_n_1796_);
if (v___x_1798_ == 0)
{
return v___x_1798_;
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1795_, v_fields_1797_);
return v___x_1799_;
}
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = 0;
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1801_, v_x_1802_);
lean_dec_ref(v_x_1802_);
lean_dec_ref(v_x_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
if (lean_obj_tag(v_x_1808_) == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = 1;
return v___x_1809_;
}
else
{
uint8_t v___x_1810_; 
v___x_1810_ = 0;
return v___x_1810_;
}
}
else
{
if (lean_obj_tag(v_x_1808_) == 0)
{
uint8_t v___x_1811_; 
v___x_1811_ = 0;
return v___x_1811_;
}
else
{
lean_object* v_head_1812_; lean_object* v_tail_1813_; lean_object* v_head_1814_; lean_object* v_tail_1815_; uint8_t v___x_1816_; 
v_head_1812_ = lean_ctor_get(v_x_1807_, 0);
v_tail_1813_ = lean_ctor_get(v_x_1807_, 1);
v_head_1814_ = lean_ctor_get(v_x_1808_, 0);
v_tail_1815_ = lean_ctor_get(v_x_1808_, 1);
v___x_1816_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1812_, v_head_1814_);
if (v___x_1816_ == 0)
{
return v___x_1816_;
}
else
{
v_x_1807_ = v_tail_1813_;
v_x_1808_ = v_tail_1815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1818_, v_x_1819_);
lean_dec(v_x_1819_);
lean_dec(v_x_1818_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
switch(lean_obj_tag(v_x_1822_))
{
case 0:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
uint8_t v___x_1824_; 
v___x_1824_ = 1;
return v___x_1824_;
}
else
{
uint8_t v___x_1825_; 
lean_dec(v_x_1823_);
v___x_1825_ = 0;
return v___x_1825_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1823_) == 1)
{
lean_object* v_kind_1826_; lean_object* v_args_1827_; lean_object* v_kind_1828_; lean_object* v_args_1829_; uint8_t v___x_1830_; 
v_kind_1826_ = lean_ctor_get(v_x_1822_, 1);
lean_inc(v_kind_1826_);
v_args_1827_ = lean_ctor_get(v_x_1822_, 2);
lean_inc_ref(v_args_1827_);
lean_dec_ref(v_x_1822_);
v_kind_1828_ = lean_ctor_get(v_x_1823_, 1);
lean_inc(v_kind_1828_);
v_args_1829_ = lean_ctor_get(v_x_1823_, 2);
lean_inc_ref(v_args_1829_);
lean_dec_ref(v_x_1823_);
v___x_1830_ = lean_name_eq(v_kind_1826_, v_kind_1828_);
lean_dec(v_kind_1828_);
lean_dec(v_kind_1826_);
if (v___x_1830_ == 0)
{
lean_dec_ref(v_args_1829_);
lean_dec_ref(v_args_1827_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = lean_array_get_size(v_args_1827_);
v___x_1832_ = lean_array_get_size(v_args_1829_);
v___x_1833_ = lean_nat_dec_eq(v___x_1831_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v_args_1829_);
lean_dec_ref(v_args_1827_);
return v___x_1833_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1827_, v_args_1829_, v___x_1831_);
lean_dec_ref(v_args_1829_);
lean_dec_ref(v_args_1827_);
return v___x_1834_;
}
}
}
else
{
uint8_t v___x_1835_; 
lean_dec_ref(v_x_1822_);
lean_dec(v_x_1823_);
v___x_1835_ = 0;
return v___x_1835_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1823_) == 2)
{
lean_object* v_val_1836_; lean_object* v_val_1837_; uint8_t v___x_1838_; 
v_val_1836_ = lean_ctor_get(v_x_1822_, 1);
lean_inc_ref(v_val_1836_);
lean_dec_ref(v_x_1822_);
v_val_1837_ = lean_ctor_get(v_x_1823_, 1);
lean_inc_ref(v_val_1837_);
lean_dec_ref(v_x_1823_);
v___x_1838_ = lean_string_dec_eq(v_val_1836_, v_val_1837_);
lean_dec_ref(v_val_1837_);
lean_dec_ref(v_val_1836_);
return v___x_1838_;
}
else
{
uint8_t v___x_1839_; 
lean_dec_ref(v_x_1822_);
lean_dec(v_x_1823_);
v___x_1839_ = 0;
return v___x_1839_;
}
}
default: 
{
if (lean_obj_tag(v_x_1823_) == 3)
{
lean_object* v_rawVal_1840_; lean_object* v_val_1841_; lean_object* v_preresolved_1842_; lean_object* v_rawVal_1843_; lean_object* v_val_1844_; lean_object* v_preresolved_1845_; uint8_t v___y_1847_; uint8_t v___x_1849_; 
v_rawVal_1840_ = lean_ctor_get(v_x_1822_, 1);
lean_inc_ref(v_rawVal_1840_);
v_val_1841_ = lean_ctor_get(v_x_1822_, 2);
lean_inc(v_val_1841_);
v_preresolved_1842_ = lean_ctor_get(v_x_1822_, 3);
lean_inc(v_preresolved_1842_);
lean_dec_ref(v_x_1822_);
v_rawVal_1843_ = lean_ctor_get(v_x_1823_, 1);
lean_inc_ref(v_rawVal_1843_);
v_val_1844_ = lean_ctor_get(v_x_1823_, 2);
lean_inc(v_val_1844_);
v_preresolved_1845_ = lean_ctor_get(v_x_1823_, 3);
lean_inc(v_preresolved_1845_);
lean_dec_ref(v_x_1823_);
v___x_1849_ = lean_substring_beq(v_rawVal_1840_, v_rawVal_1843_);
if (v___x_1849_ == 0)
{
lean_dec(v_val_1844_);
lean_dec(v_val_1841_);
v___y_1847_ = v___x_1849_;
goto v___jp_1846_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_name_eq(v_val_1841_, v_val_1844_);
lean_dec(v_val_1844_);
lean_dec(v_val_1841_);
v___y_1847_ = v___x_1850_;
goto v___jp_1846_;
}
v___jp_1846_:
{
if (v___y_1847_ == 0)
{
lean_dec(v_preresolved_1845_);
lean_dec(v_preresolved_1842_);
return v___y_1847_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1842_, v_preresolved_1845_);
lean_dec(v_preresolved_1845_);
lean_dec(v_preresolved_1842_);
return v___x_1848_;
}
}
}
else
{
uint8_t v___x_1851_; 
lean_dec_ref(v_x_1822_);
lean_dec(v_x_1823_);
v___x_1851_ = 0;
return v___x_1851_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1852_, lean_object* v_ys_1853_, lean_object* v_x_1854_){
_start:
{
lean_object* v_zero_1855_; uint8_t v_isZero_1856_; 
v_zero_1855_ = lean_unsigned_to_nat(0u);
v_isZero_1856_ = lean_nat_dec_eq(v_x_1854_, v_zero_1855_);
if (v_isZero_1856_ == 1)
{
lean_dec(v_x_1854_);
return v_isZero_1856_;
}
else
{
lean_object* v_one_1857_; lean_object* v_n_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_one_1857_ = lean_unsigned_to_nat(1u);
v_n_1858_ = lean_nat_sub(v_x_1854_, v_one_1857_);
lean_dec(v_x_1854_);
v___x_1859_ = lean_array_fget_borrowed(v_xs_1852_, v_n_1858_);
v___x_1860_ = lean_array_fget_borrowed(v_ys_1853_, v_n_1858_);
lean_inc(v___x_1860_);
lean_inc(v___x_1859_);
v___x_1861_ = l_Lean_Syntax_structEq(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_dec(v_n_1858_);
return v___x_1861_;
}
else
{
v_x_1854_ = v_n_1858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1863_, lean_object* v_ys_1864_, lean_object* v_x_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1863_, v_ys_1864_, v_x_1865_);
lean_dec_ref(v_ys_1864_);
lean_dec_ref(v_xs_1863_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
uint8_t v_res_1870_; lean_object* v_r_1871_; 
v_res_1870_ = l_Lean_Syntax_structEq(v_x_1868_, v_x_1869_);
v_r_1871_ = lean_box(v_res_1870_);
return v_r_1871_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1872_, lean_object* v_ys_1873_, lean_object* v_hsz_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1872_, v_ys_1873_, v_x_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1878_, lean_object* v_ys_1879_, lean_object* v_hsz_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
uint8_t v_res_1883_; lean_object* v_r_1884_; 
v_res_1883_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1878_, v_ys_1879_, v_hsz_1880_, v_x_1881_, v_x_1882_);
lean_dec_ref(v_ys_1879_);
lean_dec_ref(v_xs_1878_);
v_r_1884_ = lean_box(v_res_1883_);
return v_r_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1887_){
_start:
{
lean_object* v___f_1888_; 
v___f_1888_ = ((lean_object*)(l_Lean_Syntax_instBEq___closed__0));
return v___f_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Syntax_instBEqTSyntax(v_k_1889_);
lean_dec(v_k_1889_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1891_, lean_object* v_i_1892_){
_start:
{
lean_object* v_zero_1893_; uint8_t v_isZero_1894_; 
v_zero_1893_ = lean_unsigned_to_nat(0u);
v_isZero_1894_ = lean_nat_dec_eq(v_i_1892_, v_zero_1893_);
if (v_isZero_1894_ == 1)
{
lean_object* v___x_1895_; 
lean_dec(v_i_1892_);
v___x_1895_ = lean_box(0);
return v___x_1895_;
}
else
{
lean_object* v_one_1896_; lean_object* v_n_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_one_1896_ = lean_unsigned_to_nat(1u);
v_n_1897_ = lean_nat_sub(v_i_1892_, v_one_1896_);
lean_dec(v_i_1892_);
v___x_1898_ = lean_array_fget_borrowed(v_as_1891_, v_n_1897_);
v___x_1899_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1898_);
if (lean_obj_tag(v___x_1899_) == 0)
{
v_i_1892_ = v_n_1897_;
goto _start;
}
else
{
lean_dec(v_n_1897_);
return v___x_1899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1901_){
_start:
{
switch(lean_obj_tag(v_x_1901_))
{
case 2:
{
lean_object* v_info_1902_; lean_object* v___x_1903_; 
v_info_1902_ = lean_ctor_get(v_x_1901_, 0);
lean_inc(v_info_1902_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_info_1902_);
return v___x_1903_;
}
case 3:
{
lean_object* v_info_1904_; lean_object* v___x_1905_; 
v_info_1904_ = lean_ctor_get(v_x_1901_, 0);
lean_inc(v_info_1904_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_info_1904_);
return v___x_1905_;
}
case 1:
{
lean_object* v_info_1906_; 
v_info_1906_ = lean_ctor_get(v_x_1901_, 0);
if (lean_obj_tag(v_info_1906_) == 2)
{
lean_object* v_args_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_args_1907_ = lean_ctor_get(v_x_1901_, 2);
v___x_1908_ = lean_array_get_size(v_args_1907_);
v___x_1909_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1907_, v___x_1908_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
lean_inc(v_info_1906_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_info_1906_);
return v___x_1910_;
}
}
default: 
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_box(0);
return v___x_1911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1912_);
lean_dec(v_x_1912_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1914_, lean_object* v_i_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1914_, v_i_1915_);
lean_dec_ref(v_as_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1917_, lean_object* v_i_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1917_, v_i_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1921_, lean_object* v_i_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1921_, v_i_1922_, v_a_1923_);
lean_dec_ref(v_as_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_box(2);
return v___x_1927_;
}
else
{
lean_object* v_val_1928_; 
v_val_1928_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_val_1928_);
lean_dec_ref(v___x_1926_);
return v_val_1928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Syntax_getTailInfo(v_stx_1929_);
lean_dec(v_stx_1929_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1931_);
if (lean_obj_tag(v___x_1932_) == 1)
{
lean_object* v_val_1933_; 
v_val_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1933_);
lean_dec_ref(v___x_1932_);
if (lean_obj_tag(v_val_1933_) == 0)
{
lean_object* v_trailing_1934_; lean_object* v_startPos_1935_; lean_object* v_stopPos_1936_; lean_object* v___x_1937_; 
v_trailing_1934_ = lean_ctor_get(v_val_1933_, 2);
lean_inc_ref(v_trailing_1934_);
lean_dec_ref(v_val_1933_);
v_startPos_1935_ = lean_ctor_get(v_trailing_1934_, 1);
lean_inc(v_startPos_1935_);
v_stopPos_1936_ = lean_ctor_get(v_trailing_1934_, 2);
lean_inc(v_stopPos_1936_);
lean_dec_ref(v_trailing_1934_);
v___x_1937_ = lean_nat_sub(v_stopPos_1936_, v_startPos_1935_);
lean_dec(v_startPos_1935_);
lean_dec(v_stopPos_1936_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; 
lean_dec(v_val_1933_);
v___x_1938_ = lean_unsigned_to_nat(0u);
return v___x_1938_;
}
}
else
{
lean_object* v___x_1939_; 
lean_dec(v___x_1932_);
v___x_1939_ = lean_unsigned_to_nat(0u);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Syntax_getTrailingSize(v_stx_1940_);
lean_dec(v_stx_1940_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1942_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = l_Lean_Syntax_getTailInfo(v_stx_1942_);
v___x_1944_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1943_);
lean_dec(v___x_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1945_);
lean_dec(v_stx_1945_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1947_, uint8_t v_canonicalOnly_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = l_Lean_Syntax_getTailInfo(v_stx_1947_);
v___x_1950_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1949_, v_canonicalOnly_1948_);
lean_dec(v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1951_, lean_object* v_canonicalOnly_1952_){
_start:
{
uint8_t v_canonicalOnly_boxed_1953_; lean_object* v_res_1954_; 
v_canonicalOnly_boxed_1953_ = lean_unbox(v_canonicalOnly_1952_);
v_res_1954_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1951_, v_canonicalOnly_boxed_1953_);
lean_dec(v_stx_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1955_, uint8_t v_withLeading_1956_, uint8_t v_withTrailing_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Syntax_getHeadInfo(v_stx_1955_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_leading_1959_; lean_object* v_pos_1960_; lean_object* v___x_1961_; 
v_leading_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_leading_1959_);
v_pos_1960_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_pos_1960_);
lean_dec_ref(v___x_1958_);
v___x_1961_ = l_Lean_Syntax_getTailInfo(v_stx_1955_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_trailing_1962_; lean_object* v_endPos_1963_; lean_object* v_str_1964_; lean_object* v_startPos_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1979_; 
v_trailing_1962_ = lean_ctor_get(v___x_1961_, 2);
lean_inc_ref(v_trailing_1962_);
v_endPos_1963_ = lean_ctor_get(v___x_1961_, 3);
lean_inc(v_endPos_1963_);
lean_dec_ref(v___x_1961_);
v_str_1964_ = lean_ctor_get(v_leading_1959_, 0);
v_startPos_1965_ = lean_ctor_get(v_leading_1959_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_leading_1959_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v_leading_1959_, 2);
lean_dec(v_unused_1980_);
v___x_1967_ = v_leading_1959_;
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_startPos_1965_);
lean_inc(v_str_1964_);
lean_dec(v_leading_1959_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1977_; 
if (v_withLeading_1956_ == 0)
{
lean_dec(v_startPos_1965_);
v___y_1977_ = v_pos_1960_;
goto v___jp_1976_;
}
else
{
lean_dec(v_pos_1960_);
v___y_1977_ = v_startPos_1965_;
goto v___jp_1976_;
}
v___jp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 2, v___y_1971_);
lean_ctor_set(v___x_1967_, 1, v___y_1970_);
v___x_1973_ = v___x_1967_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_str_1964_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___y_1970_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v___y_1971_);
v___x_1973_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
v___jp_1976_:
{
if (v_withTrailing_1957_ == 0)
{
lean_dec_ref(v_trailing_1962_);
v___y_1970_ = v___y_1977_;
v___y_1971_ = v_endPos_1963_;
goto v___jp_1969_;
}
else
{
lean_object* v_stopPos_1978_; 
lean_dec(v_endPos_1963_);
v_stopPos_1978_ = lean_ctor_get(v_trailing_1962_, 2);
lean_inc(v_stopPos_1978_);
lean_dec_ref(v_trailing_1962_);
v___y_1970_ = v___y_1977_;
v___y_1971_ = v_stopPos_1978_;
goto v___jp_1969_;
}
}
}
}
else
{
lean_object* v___x_1981_; 
lean_dec(v___x_1961_);
lean_dec(v_pos_1960_);
lean_dec_ref(v_leading_1959_);
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v___x_1958_);
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1983_, lean_object* v_withLeading_1984_, lean_object* v_withTrailing_1985_){
_start:
{
uint8_t v_withLeading_boxed_1986_; uint8_t v_withTrailing_boxed_1987_; lean_object* v_res_1988_; 
v_withLeading_boxed_1986_ = lean_unbox(v_withLeading_1984_);
v_withTrailing_boxed_1987_ = lean_unbox(v_withTrailing_1985_);
v_res_1988_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1983_, v_withLeading_boxed_1986_, v_withTrailing_boxed_1987_);
lean_dec(v_stx_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1989_, lean_object* v_f_1990_, lean_object* v_i_1991_){
_start:
{
lean_object* v_zero_1992_; uint8_t v_isZero_1993_; 
v_zero_1992_ = lean_unsigned_to_nat(0u);
v_isZero_1993_ = lean_nat_dec_eq(v_i_1991_, v_zero_1992_);
if (v_isZero_1993_ == 1)
{
lean_object* v___x_1994_; 
lean_dec(v_i_1991_);
lean_dec_ref(v_f_1990_);
lean_dec_ref(v_a_1989_);
v___x_1994_ = lean_box(0);
return v___x_1994_;
}
else
{
lean_object* v_one_1995_; lean_object* v_n_1996_; lean_object* v_v_1997_; lean_object* v___x_1998_; 
v_one_1995_ = lean_unsigned_to_nat(1u);
v_n_1996_ = lean_nat_sub(v_i_1991_, v_one_1995_);
lean_dec(v_i_1991_);
v_v_1997_ = lean_array_fget_borrowed(v_a_1989_, v_n_1996_);
lean_inc_ref(v_f_1990_);
lean_inc(v_v_1997_);
v___x_1998_ = lean_apply_1(v_f_1990_, v_v_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
v_i_1991_ = v_n_1996_;
goto _start;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_f_1990_);
v_val_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_array_fset(v_a_1989_, v_n_1996_, v_val_2000_);
lean_dec(v_n_1996_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_2009_, lean_object* v_a_2010_, lean_object* v_f_2011_, lean_object* v_i_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_2010_, v_f_2011_, v_i_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_2014_, lean_object* v_x_2015_){
_start:
{
switch(lean_obj_tag(v_x_2015_))
{
case 2:
{
lean_object* v_val_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_val_2016_ = lean_ctor_get(v_x_2015_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_x_2015_, 0);
lean_dec(v_unused_2025_);
v___x_2018_ = v_x_2015_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_val_2016_);
lean_dec(v_x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v_info_2014_);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_info_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_val_2016_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
case 3:
{
lean_object* v_rawVal_2026_; lean_object* v_val_2027_; lean_object* v_preresolved_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2036_; 
v_rawVal_2026_ = lean_ctor_get(v_x_2015_, 1);
v_val_2027_ = lean_ctor_get(v_x_2015_, 2);
v_preresolved_2028_ = lean_ctor_get(v_x_2015_, 3);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_x_2015_, 0);
lean_dec(v_unused_2037_);
v___x_2030_ = v_x_2015_;
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_preresolved_2028_);
lean_inc(v_val_2027_);
lean_inc(v_rawVal_2026_);
lean_dec(v_x_2015_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_info_2014_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_info_2014_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_rawVal_2026_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_val_2027_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_preresolved_2028_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
case 1:
{
lean_object* v_info_2038_; lean_object* v_kind_2039_; lean_object* v_args_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2058_; 
v_info_2038_ = lean_ctor_get(v_x_2015_, 0);
v_kind_2039_ = lean_ctor_get(v_x_2015_, 1);
v_args_2040_ = lean_ctor_get(v_x_2015_, 2);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2042_ = v_x_2015_;
v_isShared_2043_ = v_isSharedCheck_2058_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_args_2040_);
lean_inc(v_kind_2039_);
lean_inc(v_info_2038_);
lean_dec(v_x_2015_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2058_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_array_get_size(v_args_2040_);
v___x_2045_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_2014_, v_args_2040_, v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; 
lean_del_object(v___x_2042_);
lean_dec(v_kind_2039_);
lean_dec(v_info_2038_);
v___x_2046_ = lean_box(0);
return v___x_2046_;
}
else
{
lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_val_2047_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 2, v_val_2047_);
v___x_2052_ = v___x_2042_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_info_2038_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_kind_2039_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_val_2047_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2052_);
v___x_2054_ = v___x_2049_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2059_; 
lean_dec(v_x_2015_);
lean_dec(v_info_2014_);
v___x_2059_ = lean_box(0);
return v___x_2059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2060_, lean_object* v_a_2061_, lean_object* v_i_2062_){
_start:
{
lean_object* v_zero_2063_; uint8_t v_isZero_2064_; 
v_zero_2063_ = lean_unsigned_to_nat(0u);
v_isZero_2064_ = lean_nat_dec_eq(v_i_2062_, v_zero_2063_);
if (v_isZero_2064_ == 1)
{
lean_object* v___x_2065_; 
lean_dec(v_i_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_info_2060_);
v___x_2065_ = lean_box(0);
return v___x_2065_;
}
else
{
lean_object* v_one_2066_; lean_object* v_n_2067_; lean_object* v_v_2068_; lean_object* v___x_2069_; 
v_one_2066_ = lean_unsigned_to_nat(1u);
v_n_2067_ = lean_nat_sub(v_i_2062_, v_one_2066_);
lean_dec(v_i_2062_);
v_v_2068_ = lean_array_fget_borrowed(v_a_2061_, v_n_2067_);
lean_inc(v_v_2068_);
lean_inc(v_info_2060_);
v___x_2069_ = l_Lean_Syntax_setTailInfoAux(v_info_2060_, v_v_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
v_i_2062_ = v_n_2067_;
goto _start;
}
else
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_info_2060_);
v_val_2071_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_array_fset(v_a_2061_, v_n_2067_, v_val_2071_);
lean_dec(v_n_2067_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2075_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2080_, lean_object* v_info_2081_){
_start:
{
lean_object* v___x_2082_; 
lean_inc(v_stx_2080_);
v___x_2082_ = l_Lean_Syntax_setTailInfoAux(v_info_2081_, v_stx_2080_);
if (lean_obj_tag(v___x_2082_) == 0)
{
return v_stx_2080_;
}
else
{
lean_object* v_val_2083_; 
lean_dec(v_stx_2080_);
v_val_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2083_);
lean_dec_ref(v___x_2082_);
return v_val_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Syntax_getTailInfo(v_stx_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_trailing_2086_; lean_object* v_leading_2087_; lean_object* v_pos_2088_; lean_object* v_endPos_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2107_; 
v_trailing_2086_ = lean_ctor_get(v___x_2085_, 2);
v_leading_2087_ = lean_ctor_get(v___x_2085_, 0);
v_pos_2088_ = lean_ctor_get(v___x_2085_, 1);
v_endPos_2089_ = lean_ctor_get(v___x_2085_, 3);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2091_ = v___x_2085_;
v_isShared_2092_ = v_isSharedCheck_2107_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_endPos_2089_);
lean_inc(v_trailing_2086_);
lean_inc(v_pos_2088_);
lean_inc(v_leading_2087_);
lean_dec(v___x_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2107_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_str_2093_; lean_object* v_startPos_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2105_; 
v_str_2093_ = lean_ctor_get(v_trailing_2086_, 0);
v_startPos_2094_ = lean_ctor_get(v_trailing_2086_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_trailing_2086_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v_trailing_2086_, 2);
lean_dec(v_unused_2106_);
v___x_2096_ = v_trailing_2086_;
v_isShared_2097_ = v_isSharedCheck_2105_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_startPos_2094_);
lean_inc(v_str_2093_);
lean_dec(v_trailing_2086_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2105_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
lean_inc(v_startPos_2094_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 2, v_startPos_2094_);
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_str_2093_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_startPos_2094_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_startPos_2094_);
v___x_2099_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 2, v___x_2099_);
v___x_2101_ = v___x_2091_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_leading_2087_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_pos_2088_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_endPos_2089_);
v___x_2101_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Syntax_setTailInfo(v_stx_2084_, v___x_2101_);
return v___x_2102_;
}
}
}
}
}
else
{
lean_dec(v___x_2085_);
return v_stx_2084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2108_, lean_object* v_f_2109_, lean_object* v_i_2110_){
_start:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_array_get_size(v_a_2108_);
v___x_2112_ = lean_nat_dec_lt(v_i_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_dec(v_i_2110_);
lean_dec_ref(v_f_2109_);
lean_dec_ref(v_a_2108_);
v___x_2113_ = lean_box(0);
return v___x_2113_;
}
else
{
lean_object* v_v_2114_; lean_object* v___x_2115_; 
v_v_2114_ = lean_array_fget_borrowed(v_a_2108_, v_i_2110_);
lean_inc_ref(v_f_2109_);
lean_inc(v_v_2114_);
v___x_2115_ = lean_apply_1(v_f_2109_, v_v_2114_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_unsigned_to_nat(1u);
v___x_2117_ = lean_nat_add(v_i_2110_, v___x_2116_);
lean_dec(v_i_2110_);
v_i_2110_ = v___x_2117_;
goto _start;
}
else
{
lean_object* v_val_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_f_2109_);
v_val_2119_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2121_ = v___x_2115_;
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_val_2119_);
lean_dec(v___x_2115_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_array_fset(v_a_2108_, v_i_2110_, v_val_2119_);
lean_dec(v_i_2110_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2123_);
v___x_2125_ = v___x_2121_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2128_, lean_object* v_inst_2129_, lean_object* v_a_2130_, lean_object* v_f_2131_, lean_object* v_i_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2130_, v_f_2131_, v_i_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_inst_2135_, lean_object* v_a_2136_, lean_object* v_f_2137_, lean_object* v_i_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2134_, v_inst_2135_, v_a_2136_, v_f_2137_, v_i_2138_);
lean_dec(v_inst_2135_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2140_, lean_object* v_x_2141_){
_start:
{
switch(lean_obj_tag(v_x_2141_))
{
case 2:
{
lean_object* v_val_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2150_; 
v_val_2142_ = lean_ctor_get(v_x_2141_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_x_2141_, 0);
lean_dec(v_unused_2151_);
v___x_2144_ = v_x_2141_;
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_val_2142_);
lean_dec(v_x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v_info_2140_);
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_info_2140_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_val_2142_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
}
case 3:
{
lean_object* v_rawVal_2152_; lean_object* v_val_2153_; lean_object* v_preresolved_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2162_; 
v_rawVal_2152_ = lean_ctor_get(v_x_2141_, 1);
v_val_2153_ = lean_ctor_get(v_x_2141_, 2);
v_preresolved_2154_ = lean_ctor_get(v_x_2141_, 3);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v_x_2141_, 0);
lean_dec(v_unused_2163_);
v___x_2156_ = v_x_2141_;
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_preresolved_2154_);
lean_inc(v_val_2153_);
lean_inc(v_rawVal_2152_);
lean_dec(v_x_2141_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_info_2140_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_info_2140_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_rawVal_2152_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_val_2153_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_preresolved_2154_);
v___x_2159_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
}
case 1:
{
lean_object* v_info_2164_; lean_object* v_kind_2165_; lean_object* v_args_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2184_; 
v_info_2164_ = lean_ctor_get(v_x_2141_, 0);
v_kind_2165_ = lean_ctor_get(v_x_2141_, 1);
v_args_2166_ = lean_ctor_get(v_x_2141_, 2);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2168_ = v_x_2141_;
v_isShared_2169_ = v_isSharedCheck_2184_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_args_2166_);
lean_inc(v_kind_2165_);
lean_inc(v_info_2164_);
lean_dec(v_x_2141_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2184_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(v_info_2140_, v_args_2166_, v___x_2170_);
if (lean_obj_tag(v___x_2171_) == 1)
{
lean_object* v_val_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2182_; 
v_val_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2182_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_val_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2182_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 2, v_val_2172_);
v___x_2177_ = v___x_2168_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_info_2164_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_kind_2165_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_val_2172_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2177_);
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v___x_2183_; 
lean_dec(v___x_2171_);
lean_del_object(v___x_2168_);
lean_dec(v_kind_2165_);
lean_dec(v_info_2164_);
v___x_2183_ = lean_box(0);
return v___x_2183_;
}
}
}
default: 
{
lean_object* v___x_2185_; 
lean_dec(v_x_2141_);
lean_dec(v_info_2140_);
v___x_2185_ = lean_box(0);
return v___x_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(lean_object* v_info_2186_, lean_object* v_a_2187_, lean_object* v_i_2188_){
_start:
{
lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_array_get_size(v_a_2187_);
v___x_2190_ = lean_nat_dec_lt(v_i_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v_i_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_info_2186_);
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
else
{
lean_object* v_v_2192_; lean_object* v___x_2193_; 
v_v_2192_ = lean_array_fget_borrowed(v_a_2187_, v_i_2188_);
lean_inc(v_v_2192_);
lean_inc(v_info_2186_);
v___x_2193_ = l_Lean_Syntax_setHeadInfoAux(v_info_2186_, v_v_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_add(v_i_2188_, v___x_2194_);
lean_dec(v_i_2188_);
v_i_2188_ = v___x_2195_;
goto _start;
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_info_2186_);
v_val_2197_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2199_ = v___x_2193_;
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v___x_2193_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_array_fset(v_a_2187_, v_i_2188_, v_val_2197_);
lean_dec(v_i_2188_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2206_, lean_object* v_inst_2207_, lean_object* v_a_2208_, lean_object* v_i_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(v_info_2206_, v_a_2208_, v_i_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___boxed(lean_object* v_info_2211_, lean_object* v_inst_2212_, lean_object* v_a_2213_, lean_object* v_i_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2211_, v_inst_2212_, v_a_2213_, v_i_2214_);
lean_dec(v_inst_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2216_, lean_object* v_info_2217_){
_start:
{
lean_object* v___x_2218_; 
lean_inc(v_stx_2216_);
v___x_2218_ = l_Lean_Syntax_setHeadInfoAux(v_info_2217_, v_stx_2216_);
if (lean_obj_tag(v___x_2218_) == 0)
{
return v_stx_2216_;
}
else
{
lean_object* v_val_2219_; 
lean_dec(v_stx_2216_);
v_val_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_val_2219_);
lean_dec_ref(v___x_2218_);
return v_val_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2220_, lean_object* v_x_2221_){
_start:
{
switch(lean_obj_tag(v_x_2221_))
{
case 0:
{
lean_dec(v_info_2220_);
return v_x_2221_;
}
case 1:
{
lean_object* v_kind_2222_; lean_object* v_args_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_kind_2222_ = lean_ctor_get(v_x_2221_, 1);
v_args_2223_ = lean_ctor_get(v_x_2221_, 2);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_x_2221_, 0);
lean_dec(v_unused_2231_);
v___x_2225_ = v_x_2221_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_args_2223_);
lean_inc(v_kind_2222_);
lean_dec(v_x_2221_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_info_2220_);
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_info_2220_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_kind_2222_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_args_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
case 2:
{
lean_object* v_val_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
v_val_2232_ = lean_ctor_get(v_x_2221_, 1);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v_x_2221_, 0);
lean_dec(v_unused_2240_);
v___x_2234_ = v_x_2221_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_val_2232_);
lean_dec(v_x_2221_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_info_2220_);
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_info_2220_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_val_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
default: 
{
lean_object* v_rawVal_2241_; lean_object* v_val_2242_; lean_object* v_preresolved_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_rawVal_2241_ = lean_ctor_get(v_x_2221_, 1);
v_val_2242_ = lean_ctor_get(v_x_2221_, 2);
v_preresolved_2243_ = lean_ctor_get(v_x_2221_, 3);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v_x_2221_, 0);
lean_dec(v_unused_2251_);
v___x_2245_ = v_x_2221_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_preresolved_2243_);
lean_inc(v_val_2242_);
lean_inc(v_rawVal_2241_);
lean_dec(v_x_2221_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v_info_2220_);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_info_2220_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_rawVal_2241_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_val_2242_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_preresolved_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2255_){
_start:
{
switch(lean_obj_tag(v_x_2255_))
{
case 2:
{
lean_object* v_info_2256_; uint8_t v___x_2257_; lean_object* v___x_2258_; 
v_info_2256_ = lean_ctor_get(v_x_2255_, 0);
v___x_2257_ = 0;
v___x_2258_ = l_Lean_SourceInfo_getPos_x3f(v_info_2256_, v___x_2257_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref(v_x_2255_);
v___x_2259_ = lean_box(0);
return v___x_2259_;
}
else
{
lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; 
v_unused_2267_ = lean_ctor_get(v___x_2258_, 0);
lean_dec(v_unused_2267_);
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v_x_2255_);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_x_2255_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
case 3:
{
lean_object* v_info_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; 
v_info_2268_ = lean_ctor_get(v_x_2255_, 0);
v___x_2269_ = 0;
v___x_2270_ = l_Lean_SourceInfo_getPos_x3f(v_info_2268_, v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
lean_dec_ref(v_x_2255_);
v___x_2271_ = lean_box(0);
return v___x_2271_;
}
else
{
lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; 
v_unused_2279_ = lean_ctor_get(v___x_2270_, 0);
lean_dec(v_unused_2279_);
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v_x_2255_);
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_x_2255_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
case 1:
{
lean_object* v_info_2280_; 
v_info_2280_ = lean_ctor_get(v_x_2255_, 0);
if (lean_obj_tag(v_info_2280_) == 2)
{
lean_object* v_args_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; size_t v_sz_2284_; size_t v___x_2285_; lean_object* v___x_2286_; lean_object* v_fst_2287_; 
v_args_2281_ = lean_ctor_get(v_x_2255_, 2);
lean_inc_ref(v_args_2281_);
lean_dec_ref(v_x_2255_);
v___x_2282_ = lean_box(0);
v___x_2283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2284_ = lean_array_size(v_args_2281_);
v___x_2285_ = ((size_t)0ULL);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2281_, v_sz_2284_, v___x_2285_, v___x_2283_);
lean_dec_ref(v_args_2281_);
v_fst_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_fst_2287_);
lean_dec_ref(v___x_2286_);
if (lean_obj_tag(v_fst_2287_) == 0)
{
return v___x_2282_;
}
else
{
lean_object* v_val_2288_; 
v_val_2288_ = lean_ctor_get(v_fst_2287_, 0);
lean_inc(v_val_2288_);
lean_dec_ref(v_fst_2287_);
return v_val_2288_;
}
}
else
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_x_2255_);
return v___x_2289_;
}
}
default: 
{
lean_object* v___x_2290_; 
lean_dec(v_x_2255_);
v___x_2290_ = lean_box(0);
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_b_2294_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_usize_dec_lt(v_i_2293_, v_sz_2292_);
if (v___x_2295_ == 0)
{
return v_b_2294_;
}
else
{
lean_object* v___x_2296_; lean_object* v_a_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v_b_2294_);
v___x_2296_ = lean_box(0);
v_a_2297_ = lean_array_uget_borrowed(v_as_2291_, v_i_2293_);
lean_inc(v_a_2297_);
v___x_2298_ = l_Lean_Syntax_getHead_x3f(v_a_2297_);
if (lean_obj_tag(v___x_2298_) == 1)
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2296_);
return v___x_2300_;
}
else
{
lean_object* v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; 
lean_dec(v___x_2298_);
v___x_2301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_add(v_i_2293_, v___x_2302_);
v_i_2293_ = v___x_2303_;
v_b_2294_ = v___x_2301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2305_, lean_object* v_sz_2306_, lean_object* v_i_2307_, lean_object* v_b_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2306_);
lean_dec(v_sz_2306_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2305_, v_sz_boxed_2309_, v_i_boxed_2310_, v_b_2308_);
lean_dec_ref(v_as_2305_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2312_, lean_object* v_source_2313_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = l_Lean_Syntax_getHeadInfo(v_source_2313_);
v___x_2315_ = l_Lean_Syntax_setHeadInfo(v_target_2312_, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_getTailInfo(v_source_2313_);
v___x_2317_ = l_Lean_Syntax_setTailInfo(v___x_2315_, v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2318_, lean_object* v_source_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2318_, v_source_2319_);
lean_dec(v_source_2319_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2321_){
_start:
{
uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = 0;
v___x_2323_ = l_Lean_SourceInfo_fromRef(v_stx_2321_, v___x_2322_);
v___x_2324_ = l_Lean_Syntax_setHeadInfo(v_stx_2321_, v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2325_, lean_object* v_withRef_2326_, lean_object* v_x_2327_, lean_object* v_oldRef_2328_){
_start:
{
lean_object* v_ref_2329_; lean_object* v___x_2330_; 
v_ref_2329_ = l_Lean_replaceRef(v_val_2325_, v_oldRef_2328_);
v___x_2330_ = lean_apply_3(v_withRef_2326_, lean_box(0), v_ref_2329_, v_x_2327_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2331_, lean_object* v_withRef_2332_, lean_object* v_x_2333_, lean_object* v_oldRef_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2331_, v_withRef_2332_, v_x_2333_, v_oldRef_2334_);
lean_dec(v_oldRef_2334_);
lean_dec(v_val_2331_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2336_, lean_object* v_withRef_2337_, lean_object* v_toBind_2338_, lean_object* v_getRef_2339_, lean_object* v_____do__lift_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_dec(v_getRef_2339_);
lean_dec(v_toBind_2338_);
lean_dec(v_withRef_2337_);
return v_x_2336_;
}
else
{
lean_object* v_val_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; 
v_val_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_val_2342_);
lean_dec_ref(v___x_2341_);
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2343_, 0, v_val_2342_);
lean_closure_set(v___f_2343_, 1, v_withRef_2337_);
lean_closure_set(v___f_2343_, 2, v_x_2336_);
v___x_2344_ = lean_apply_4(v_toBind_2338_, lean_box(0), lean_box(0), v_getRef_2339_, v___f_2343_);
return v___x_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v_toBind_2348_; lean_object* v_getRef_2349_; lean_object* v_withRef_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; 
v_toBind_2348_ = lean_ctor_get(v_inst_2345_, 1);
lean_inc(v_toBind_2348_);
lean_dec_ref(v_inst_2345_);
v_getRef_2349_ = lean_ctor_get(v_inst_2346_, 0);
lean_inc(v_getRef_2349_);
v_withRef_2350_ = lean_ctor_get(v_inst_2346_, 1);
lean_inc(v_withRef_2350_);
lean_dec_ref(v_inst_2346_);
lean_inc(v_getRef_2349_);
lean_inc(v_toBind_2348_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2351_, 0, v_x_2347_);
lean_closure_set(v___f_2351_, 1, v_withRef_2350_);
lean_closure_set(v___f_2351_, 2, v_toBind_2348_);
lean_closure_set(v___f_2351_, 3, v_getRef_2349_);
v___x_2352_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v_getRef_2349_, v___f_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_00_u03b1_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v_toBind_2358_; lean_object* v_getRef_2359_; lean_object* v_withRef_2360_; lean_object* v___f_2361_; lean_object* v___x_2362_; 
v_toBind_2358_ = lean_ctor_get(v_inst_2354_, 1);
lean_inc(v_toBind_2358_);
lean_dec_ref(v_inst_2354_);
v_getRef_2359_ = lean_ctor_get(v_inst_2355_, 0);
lean_inc(v_getRef_2359_);
v_withRef_2360_ = lean_ctor_get(v_inst_2355_, 1);
lean_inc(v_withRef_2360_);
lean_dec_ref(v_inst_2355_);
lean_inc(v_getRef_2359_);
lean_inc(v_toBind_2358_);
v___f_2361_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2361_, 0, v_x_2357_);
lean_closure_set(v___f_2361_, 1, v_withRef_2360_);
lean_closure_set(v___f_2361_, 2, v_toBind_2358_);
lean_closure_set(v___f_2361_, 3, v_getRef_2359_);
v___x_2362_ = lean_apply_4(v_toBind_2358_, lean_box(0), lean_box(0), v_getRef_2359_, v___f_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2372_, lean_object* v_k_2373_){
_start:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2375_ = lean_name_eq(v_k_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
return v___x_2372_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = 0;
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2377_, lean_object* v_k_2378_){
_start:
{
uint8_t v___x_1982__boxed_2379_; uint8_t v_res_2380_; lean_object* v_r_2381_; 
v___x_1982__boxed_2379_ = lean_unbox(v___x_2377_);
v_res_2380_ = l_Lean_expandMacros___lam__0(v___x_1982__boxed_2379_, v_k_2378_);
lean_dec(v_k_2378_);
v_r_2381_ = lean_box(v_res_2380_);
return v_r_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2383_, lean_object* v_p_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
if (lean_obj_tag(v_stx_2383_) == 1)
{
lean_object* v_info_2387_; lean_object* v_kind_2388_; lean_object* v_args_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v_info_2387_ = lean_ctor_get(v_stx_2383_, 0);
v_kind_2388_ = lean_ctor_get(v_stx_2383_, 1);
v_args_2389_ = lean_ctor_get(v_stx_2383_, 2);
lean_inc(v_kind_2388_);
v___x_2390_ = lean_apply_1(v_p_2384_, v_kind_2388_);
v___x_2391_ = lean_unbox(v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
lean_dec_ref(v_a_2385_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_stx_2383_);
lean_ctor_set(v___x_2392_, 1, v_a_2386_);
return v___x_2392_;
}
else
{
lean_object* v_methods_2393_; lean_object* v_quotContext_2394_; lean_object* v_currMacroScope_2395_; lean_object* v_currRecDepth_2396_; lean_object* v_maxRecDepth_2397_; lean_object* v_ref_2398_; lean_object* v_ref_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_methods_2393_ = lean_ctor_get(v_a_2385_, 0);
lean_inc(v_methods_2393_);
v_quotContext_2394_ = lean_ctor_get(v_a_2385_, 1);
lean_inc(v_quotContext_2394_);
v_currMacroScope_2395_ = lean_ctor_get(v_a_2385_, 2);
lean_inc(v_currMacroScope_2395_);
v_currRecDepth_2396_ = lean_ctor_get(v_a_2385_, 3);
lean_inc(v_currRecDepth_2396_);
v_maxRecDepth_2397_ = lean_ctor_get(v_a_2385_, 4);
lean_inc(v_maxRecDepth_2397_);
v_ref_2398_ = lean_ctor_get(v_a_2385_, 5);
lean_inc(v_ref_2398_);
lean_dec_ref(v_a_2385_);
v_ref_2399_ = l_Lean_replaceRef(v_stx_2383_, v_ref_2398_);
lean_dec(v_ref_2398_);
lean_inc(v_ref_2399_);
lean_inc(v_maxRecDepth_2397_);
lean_inc(v_currRecDepth_2396_);
lean_inc(v_currMacroScope_2395_);
lean_inc(v_quotContext_2394_);
lean_inc(v_methods_2393_);
v___x_2400_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2400_, 0, v_methods_2393_);
lean_ctor_set(v___x_2400_, 1, v_quotContext_2394_);
lean_ctor_set(v___x_2400_, 2, v_currMacroScope_2395_);
lean_ctor_set(v___x_2400_, 3, v_currRecDepth_2396_);
lean_ctor_set(v___x_2400_, 4, v_maxRecDepth_2397_);
lean_ctor_set(v___x_2400_, 5, v_ref_2399_);
lean_inc_ref(v_stx_2383_);
v___x_2401_ = l_Lean_Macro_expandMacro_x3f(v_stx_2383_, v___x_2400_, v_a_2386_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
if (lean_obj_tag(v_a_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v___x_2400_);
v_a_2403_ = lean_ctor_get(v___x_2401_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v___x_2401_, 0);
lean_dec(v_unused_2449_);
v___x_2405_ = v___x_2401_;
v_isShared_2406_ = v_isSharedCheck_2448_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2401_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2448_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_nat_dec_eq(v_currRecDepth_2396_, v_maxRecDepth_2397_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2439_; 
lean_inc_ref(v_args_2389_);
lean_inc(v_kind_2388_);
lean_inc(v_info_2387_);
lean_del_object(v___x_2405_);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_stx_2383_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; lean_object* v_unused_2441_; lean_object* v_unused_2442_; 
v_unused_2440_ = lean_ctor_get(v_stx_2383_, 2);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_stx_2383_, 1);
lean_dec(v_unused_2441_);
v_unused_2442_ = lean_ctor_get(v_stx_2383_, 0);
lean_dec(v_unused_2442_);
v___x_2409_ = v_stx_2383_;
v_isShared_2410_ = v_isSharedCheck_2439_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v_stx_2383_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2439_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; size_t v_sz_2414_; size_t v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = lean_nat_add(v_currRecDepth_2396_, v___x_2411_);
lean_dec(v_currRecDepth_2396_);
v___x_2413_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2413_, 0, v_methods_2393_);
lean_ctor_set(v___x_2413_, 1, v_quotContext_2394_);
lean_ctor_set(v___x_2413_, 2, v_currMacroScope_2395_);
lean_ctor_set(v___x_2413_, 3, v___x_2412_);
lean_ctor_set(v___x_2413_, 4, v_maxRecDepth_2397_);
lean_ctor_set(v___x_2413_, 5, v_ref_2399_);
v_sz_2414_ = lean_array_size(v_args_2389_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_unbox(v___x_2390_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2416_, v_sz_2414_, v___x_2415_, v_args_2389_, v___x_2413_, v_a_2403_);
lean_dec_ref(v___x_2413_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2429_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_a_2419_ = lean_ctor_get(v___x_2417_, 1);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2421_ = v___x_2417_;
v_isShared_2422_ = v_isSharedCheck_2429_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2429_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 2, v_a_2418_);
v___x_2424_ = v___x_2409_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_info_2387_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_kind_2388_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_a_2418_);
v___x_2424_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2424_);
v___x_2426_ = v___x_2421_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_a_2419_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_del_object(v___x_2409_);
lean_dec(v_kind_2388_);
lean_dec(v_info_2387_);
v_a_2430_ = lean_ctor_get(v___x_2417_, 0);
v_a_2431_ = lean_ctor_get(v___x_2417_, 1);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2417_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_inc(v_a_2430_);
lean_dec(v___x_2417_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2430_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec(v_ref_2399_);
lean_dec(v_maxRecDepth_2397_);
lean_dec(v_currRecDepth_2396_);
lean_dec(v_currMacroScope_2395_);
lean_dec(v_quotContext_2394_);
lean_dec(v_methods_2393_);
v___x_2443_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v_stx_2383_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 1);
lean_ctor_set(v___x_2405_, 0, v___x_2444_);
v___x_2446_ = v___x_2405_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_a_2403_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v_val_2451_; lean_object* v___f_2452_; 
lean_dec(v_ref_2399_);
lean_dec(v_maxRecDepth_2397_);
lean_dec(v_currRecDepth_2396_);
lean_dec(v_currMacroScope_2395_);
lean_dec(v_quotContext_2394_);
lean_dec(v_methods_2393_);
lean_dec_ref(v_stx_2383_);
v_a_2450_ = lean_ctor_get(v___x_2401_, 1);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2401_);
v_val_2451_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_val_2451_);
lean_dec_ref(v_a_2402_);
v___f_2452_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2452_, 0, v___x_2390_);
v_stx_2383_ = v_val_2451_;
v_p_2384_ = v___f_2452_;
v_a_2385_ = v___x_2400_;
v_a_2386_ = v_a_2450_;
goto _start;
}
}
else
{
lean_object* v_a_2454_; lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v___x_2400_);
lean_dec(v_ref_2399_);
lean_dec(v_maxRecDepth_2397_);
lean_dec(v_currRecDepth_2396_);
lean_dec(v_currMacroScope_2395_);
lean_dec(v_quotContext_2394_);
lean_dec(v_methods_2393_);
lean_dec_ref(v_stx_2383_);
v_a_2454_ = lean_ctor_get(v___x_2401_, 0);
v_a_2455_ = lean_ctor_get(v___x_2401_, 1);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2401_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_inc(v_a_2454_);
lean_dec(v___x_2401_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2454_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
else
{
lean_object* v___x_2463_; 
lean_dec_ref(v_a_2385_);
lean_dec_ref(v_p_2384_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_stx_2383_);
lean_ctor_set(v___x_2463_, 1, v_a_2386_);
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2464_, size_t v_sz_2465_, size_t v_i_2466_, lean_object* v_bs_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_usize_dec_lt(v_i_2466_, v_sz_2465_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_bs_2467_);
lean_ctor_set(v___x_2471_, 1, v___y_2469_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v_v_2474_; lean_object* v___x_2475_; 
v___x_2472_ = lean_box(v___x_2464_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2473_, 0, v___x_2472_);
v_v_2474_ = lean_array_uget_borrowed(v_bs_2467_, v_i_2466_);
lean_inc_ref(v___y_2468_);
lean_inc(v_v_2474_);
v___x_2475_ = l_Lean_expandMacros(v_v_2474_, v___f_2473_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v_bs_x27_2479_; size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
v_a_2477_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2475_);
v___x_2478_ = lean_unsigned_to_nat(0u);
v_bs_x27_2479_ = lean_array_uset(v_bs_2467_, v_i_2466_, v___x_2478_);
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2466_, v___x_2480_);
v___x_2482_ = lean_array_uset(v_bs_x27_2479_, v_i_2466_, v_a_2476_);
v_i_2466_ = v___x_2481_;
v_bs_2467_ = v___x_2482_;
v___y_2469_ = v_a_2477_;
goto _start;
}
else
{
lean_object* v_a_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_bs_2467_);
v_a_2484_ = lean_ctor_get(v___x_2475_, 0);
v_a_2485_ = lean_ctor_get(v___x_2475_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2475_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_inc(v_a_2484_);
lean_dec(v___x_2475_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2484_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_bs_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v___x_2001__boxed_2499_; size_t v_sz_boxed_2500_; size_t v_i_boxed_2501_; lean_object* v_res_2502_; 
v___x_2001__boxed_2499_ = lean_unbox(v___x_2493_);
v_sz_boxed_2500_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2501_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2001__boxed_2499_, v_sz_boxed_2500_, v_i_boxed_2501_, v_bs_2496_, v___y_2497_, v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2503_, lean_object* v_val_2504_, uint8_t v_canonical_2505_){
_start:
{
lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2506_ = l_Lean_SourceInfo_fromRef(v_src_2503_, v_canonical_2505_);
v___x_2507_ = 1;
lean_inc(v_val_2504_);
v___x_2508_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2504_, v___x_2507_);
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = lean_string_utf8_byte_size(v___x_2508_);
v___x_2511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2508_);
lean_ctor_set(v___x_2511_, 1, v___x_2509_);
lean_ctor_set(v___x_2511_, 2, v___x_2510_);
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2506_);
lean_ctor_set(v___x_2513_, 1, v___x_2511_);
lean_ctor_set(v___x_2513_, 2, v_val_2504_);
lean_ctor_set(v___x_2513_, 3, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2514_, lean_object* v_val_2515_, lean_object* v_canonical_2516_){
_start:
{
uint8_t v_canonical_boxed_2517_; lean_object* v_res_2518_; 
v_canonical_boxed_2517_ = lean_unbox(v_canonical_2516_);
v_res_2518_ = l_Lean_mkIdentFrom(v_src_2514_, v_val_2515_, v_canonical_boxed_2517_);
lean_dec(v_src_2514_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2519_, uint8_t v_canonical_2520_, lean_object* v_toPure_2521_, lean_object* v_____do__lift_2522_){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = l_Lean_mkIdentFrom(v_____do__lift_2522_, v_val_2519_, v_canonical_2520_);
v___x_2524_ = lean_apply_2(v_toPure_2521_, lean_box(0), v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2525_, lean_object* v_canonical_2526_, lean_object* v_toPure_2527_, lean_object* v_____do__lift_2528_){
_start:
{
uint8_t v_canonical_boxed_2529_; lean_object* v_res_2530_; 
v_canonical_boxed_2529_ = lean_unbox(v_canonical_2526_);
v_res_2530_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2525_, v_canonical_boxed_2529_, v_toPure_2527_, v_____do__lift_2528_);
lean_dec(v_____do__lift_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_val_2533_, uint8_t v_canonical_2534_){
_start:
{
lean_object* v_toApplicative_2535_; lean_object* v_toBind_2536_; lean_object* v_getRef_2537_; lean_object* v_toPure_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; lean_object* v___x_2541_; 
v_toApplicative_2535_ = lean_ctor_get(v_inst_2531_, 0);
lean_inc_ref(v_toApplicative_2535_);
v_toBind_2536_ = lean_ctor_get(v_inst_2531_, 1);
lean_inc(v_toBind_2536_);
lean_dec_ref(v_inst_2531_);
v_getRef_2537_ = lean_ctor_get(v_inst_2532_, 0);
lean_inc(v_getRef_2537_);
lean_dec_ref(v_inst_2532_);
v_toPure_2538_ = lean_ctor_get(v_toApplicative_2535_, 1);
lean_inc(v_toPure_2538_);
lean_dec_ref(v_toApplicative_2535_);
v___x_2539_ = lean_box(v_canonical_2534_);
v___f_2540_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2540_, 0, v_val_2533_);
lean_closure_set(v___f_2540_, 1, v___x_2539_);
lean_closure_set(v___f_2540_, 2, v_toPure_2538_);
v___x_2541_ = lean_apply_4(v_toBind_2536_, lean_box(0), lean_box(0), v_getRef_2537_, v___f_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_val_2544_, lean_object* v_canonical_2545_){
_start:
{
uint8_t v_canonical_boxed_2546_; lean_object* v_res_2547_; 
v_canonical_boxed_2546_ = lean_unbox(v_canonical_2545_);
v_res_2547_ = l_Lean_mkIdentFromRef___redArg(v_inst_2542_, v_inst_2543_, v_val_2544_, v_canonical_boxed_2546_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_val_2551_, uint8_t v_canonical_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_mkIdentFromRef___redArg(v_inst_2549_, v_inst_2550_, v_val_2551_, v_canonical_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_val_2557_, lean_object* v_canonical_2558_){
_start:
{
uint8_t v_canonical_boxed_2559_; lean_object* v_res_2560_; 
v_canonical_boxed_2559_ = lean_unbox(v_canonical_2558_);
v_res_2560_ = l_Lean_mkIdentFromRef(v_m_2554_, v_inst_2555_, v_inst_2556_, v_val_2557_, v_canonical_boxed_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2564_, lean_object* v_c_2565_, uint8_t v_canonical_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_id_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2567_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2568_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2565_);
v_id_2569_ = l_Lean_addMacroScope(v___x_2567_, v_c_2565_, v___x_2568_);
v___x_2570_ = l_Lean_SourceInfo_fromRef(v_src_2564_, v_canonical_2566_);
v___x_2571_ = 1;
lean_inc(v_id_2569_);
v___x_2572_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2569_, v___x_2571_);
v___x_2573_ = lean_string_utf8_byte_size(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2568_);
lean_ctor_set(v___x_2574_, 2, v___x_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_c_2565_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2575_);
v___x_2578_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2570_);
lean_ctor_set(v___x_2578_, 1, v___x_2574_);
lean_ctor_set(v___x_2578_, 2, v_id_2569_);
lean_ctor_set(v___x_2578_, 3, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2579_, lean_object* v_c_2580_, lean_object* v_canonical_2581_){
_start:
{
uint8_t v_canonical_boxed_2582_; lean_object* v_res_2583_; 
v_canonical_boxed_2582_ = lean_unbox(v_canonical_2581_);
v_res_2583_ = l_Lean_mkCIdentFrom(v_src_2579_, v_c_2580_, v_canonical_boxed_2582_);
lean_dec(v_src_2579_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2584_, uint8_t v_canonical_2585_, lean_object* v_toPure_2586_, lean_object* v_____do__lift_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = l_Lean_mkCIdentFrom(v_____do__lift_2587_, v_c_2584_, v_canonical_2585_);
v___x_2589_ = lean_apply_2(v_toPure_2586_, lean_box(0), v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2590_, lean_object* v_canonical_2591_, lean_object* v_toPure_2592_, lean_object* v_____do__lift_2593_){
_start:
{
uint8_t v_canonical_boxed_2594_; lean_object* v_res_2595_; 
v_canonical_boxed_2594_ = lean_unbox(v_canonical_2591_);
v_res_2595_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2590_, v_canonical_boxed_2594_, v_toPure_2592_, v_____do__lift_2593_);
lean_dec(v_____do__lift_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_c_2598_, uint8_t v_canonical_2599_){
_start:
{
lean_object* v_toApplicative_2600_; lean_object* v_toBind_2601_; lean_object* v_getRef_2602_; lean_object* v_toPure_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; 
v_toApplicative_2600_ = lean_ctor_get(v_inst_2596_, 0);
lean_inc_ref(v_toApplicative_2600_);
v_toBind_2601_ = lean_ctor_get(v_inst_2596_, 1);
lean_inc(v_toBind_2601_);
lean_dec_ref(v_inst_2596_);
v_getRef_2602_ = lean_ctor_get(v_inst_2597_, 0);
lean_inc(v_getRef_2602_);
lean_dec_ref(v_inst_2597_);
v_toPure_2603_ = lean_ctor_get(v_toApplicative_2600_, 1);
lean_inc(v_toPure_2603_);
lean_dec_ref(v_toApplicative_2600_);
v___x_2604_ = lean_box(v_canonical_2599_);
v___f_2605_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2605_, 0, v_c_2598_);
lean_closure_set(v___f_2605_, 1, v___x_2604_);
lean_closure_set(v___f_2605_, 2, v_toPure_2603_);
v___x_2606_ = lean_apply_4(v_toBind_2601_, lean_box(0), lean_box(0), v_getRef_2602_, v___f_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_c_2609_, lean_object* v_canonical_2610_){
_start:
{
uint8_t v_canonical_boxed_2611_; lean_object* v_res_2612_; 
v_canonical_boxed_2611_ = lean_unbox(v_canonical_2610_);
v_res_2612_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2607_, v_inst_2608_, v_c_2609_, v_canonical_boxed_2611_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_c_2616_, uint8_t v_canonical_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2614_, v_inst_2615_, v_c_2616_, v_canonical_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_c_2622_, lean_object* v_canonical_2623_){
_start:
{
uint8_t v_canonical_boxed_2624_; lean_object* v_res_2625_; 
v_canonical_boxed_2624_ = lean_unbox(v_canonical_2623_);
v_res_2625_ = l_Lean_mkCIdentFromRef(v_m_2619_, v_inst_2620_, v_inst_2621_, v_c_2622_, v_canonical_boxed_2624_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_box(0);
v___x_2628_ = 0;
v___x_2629_ = l_Lean_mkCIdentFrom(v___x_2627_, v_c_2626_, v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* lean_mk_syntax_ident(lean_object* v_val_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2631_ = lean_box(2);
v___x_2632_ = 1;
lean_inc(v_val_2630_);
v___x_2633_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2630_, v___x_2632_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_string_utf8_byte_size(v___x_2633_);
v___x_2636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2633_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v___x_2635_);
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2631_);
lean_ctor_set(v___x_2638_, 1, v___x_2636_);
lean_ctor_set(v___x_2638_, 2, v_val_2630_);
lean_ctor_set(v___x_2638_, 3, v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2644_ = lean_box(2);
v___x_2645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v___x_2643_);
lean_ctor_set(v___x_2645_, 2, v_args_2642_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2646_, lean_object* v_as_2647_, size_t v_sz_2648_, size_t v_i_2649_, lean_object* v_b_2650_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_usize_dec_lt(v_i_2649_, v_sz_2648_);
if (v___x_2651_ == 0)
{
lean_dec(v_sep_2646_);
return v_b_2650_;
}
else
{
lean_object* v_fst_2652_; lean_object* v_snd_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2673_; 
v_fst_2652_ = lean_ctor_get(v_b_2650_, 0);
v_snd_2653_ = lean_ctor_get(v_b_2650_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_b_2650_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2655_ = v_b_2650_;
v_isShared_2656_ = v_isSharedCheck_2673_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2653_);
lean_inc(v_fst_2652_);
lean_dec(v_b_2650_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2673_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_r_2658_; lean_object* v_i_2667_; lean_object* v_a_2668_; uint8_t v___x_2669_; 
v_i_2667_ = lean_unsigned_to_nat(0u);
v_a_2668_ = lean_array_uget_borrowed(v_as_2647_, v_i_2649_);
v___x_2669_ = lean_nat_dec_lt(v_i_2667_, v_fst_2652_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_inc(v_a_2668_);
v___x_2670_ = lean_array_push(v_snd_2653_, v_a_2668_);
v_r_2658_ = v___x_2670_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_inc(v_sep_2646_);
v___x_2671_ = lean_array_push(v_snd_2653_, v_sep_2646_);
lean_inc(v_a_2668_);
v___x_2672_ = lean_array_push(v___x_2671_, v_a_2668_);
v_r_2658_ = v___x_2672_;
goto v___jp_2657_;
}
v___jp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = lean_unsigned_to_nat(1u);
v___x_2660_ = lean_nat_add(v_fst_2652_, v___x_2659_);
lean_dec(v_fst_2652_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v_r_2658_);
lean_ctor_set(v___x_2655_, 0, v___x_2660_);
v___x_2662_ = v___x_2655_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_r_2658_);
v___x_2662_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
size_t v___x_2663_; size_t v___x_2664_; 
v___x_2663_ = ((size_t)1ULL);
v___x_2664_ = lean_usize_add(v_i_2649_, v___x_2663_);
v_i_2649_ = v___x_2664_;
v_b_2650_ = v___x_2662_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2674_, lean_object* v_as_2675_, lean_object* v_sz_2676_, lean_object* v_i_2677_, lean_object* v_b_2678_){
_start:
{
size_t v_sz_boxed_2679_; size_t v_i_boxed_2680_; lean_object* v_res_2681_; 
v_sz_boxed_2679_ = lean_unbox_usize(v_sz_2676_);
lean_dec(v_sz_2676_);
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2674_, v_as_2675_, v_sz_boxed_2679_, v_i_boxed_2680_, v_b_2678_);
lean_dec_ref(v_as_2675_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2687_, lean_object* v_sep_2688_){
_start:
{
lean_object* v___x_2689_; size_t v_sz_2690_; size_t v___x_2691_; lean_object* v___x_2692_; lean_object* v_snd_2693_; 
v___x_2689_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2690_ = lean_array_size(v_as_2687_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2688_, v_as_2687_, v_sz_2690_, v___x_2691_, v___x_2689_);
v_snd_2693_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_snd_2693_);
lean_dec_ref(v___x_2692_);
return v_snd_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2694_, lean_object* v_sep_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_mkSepArray(v_as_2694_, v_sep_2695_);
lean_dec_ref(v_as_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2704_){
_start:
{
if (lean_obj_tag(v_arg_2704_) == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2705_;
}
else
{
lean_object* v_val_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_val_2706_ = lean_ctor_get(v_arg_2704_, 0);
lean_inc(v_val_2706_);
lean_dec_ref(v_arg_2704_);
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2709_ = lean_array_push(v___x_2708_, v_val_2706_);
v___x_2710_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2711_ = lean_box(2);
v___x_2712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___x_2710_);
lean_ctor_set(v___x_2712_, 2, v___x_2709_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2719_, uint8_t v_canonical_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2721_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2722_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2723_ = l_Lean_mkAtomFrom(v_ref_2719_, v___x_2722_, v_canonical_2720_);
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_mk_empty_array_with_capacity(v___x_2724_);
v___x_2726_ = lean_array_push(v___x_2725_, v___x_2723_);
v___x_2727_ = lean_box(2);
v___x_2728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___x_2721_);
lean_ctor_set(v___x_2728_, 2, v___x_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2729_, lean_object* v_canonical_2730_){
_start:
{
uint8_t v_canonical_boxed_2731_; lean_object* v_res_2732_; 
v_canonical_boxed_2731_ = lean_unbox(v_canonical_2730_);
v_res_2732_ = l_Lean_mkHole(v_ref_2729_, v_canonical_boxed_2731_);
lean_dec(v_ref_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2733_, lean_object* v_sep_2734_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2735_ = l_Lean_mkSepArray(v_a_2733_, v_sep_2734_);
v___x_2736_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2737_ = lean_box(2);
v___x_2738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v___x_2736_);
lean_ctor_set(v___x_2738_, 2, v___x_2735_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2739_, lean_object* v_sep_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Syntax_mkSep(v_a_2739_, v_sep_2740_);
lean_dec_ref(v_a_2739_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2748_, lean_object* v_elems_2749_){
_start:
{
uint8_t v___x_2750_; 
lean_inc_ref(v_sep_2748_);
v___x_2750_ = lean_string_isempty(v_sep_2748_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = l_Lean_mkAtom(v_sep_2748_);
v___x_2752_ = l_Lean_mkSepArray(v_elems_2749_, v___x_2751_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec_ref(v_sep_2748_);
v___x_2753_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2754_ = l_Lean_mkSepArray(v_elems_2749_, v___x_2753_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2755_, lean_object* v_elems_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2755_, v_elems_2756_);
lean_dec_ref(v_elems_2756_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2758_, lean_object* v_toPure_2759_, lean_object* v_sep_2760_, lean_object* v_ref_2761_){
_start:
{
lean_object* v___y_2763_; uint8_t v___x_2766_; 
lean_inc_ref(v_sep_2760_);
v___x_2766_ = lean_string_isempty(v_sep_2760_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_mkAtomFrom(v_ref_2761_, v_sep_2760_, v___x_2766_);
v___y_2763_ = v___x_2767_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2768_; 
lean_dec_ref(v_sep_2760_);
v___x_2768_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2763_ = v___x_2768_;
goto v___jp_2762_;
}
v___jp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = l_Lean_mkSepArray(v_elems_2758_, v___y_2763_);
v___x_2765_ = lean_apply_2(v_toPure_2759_, lean_box(0), v___x_2764_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2769_, lean_object* v_toPure_2770_, lean_object* v_sep_2771_, lean_object* v_ref_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2769_, v_toPure_2770_, v_sep_2771_, v_ref_2772_);
lean_dec(v_ref_2772_);
lean_dec_ref(v_elems_2769_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2774_, lean_object* v_inst_2775_, lean_object* v_sep_2776_, lean_object* v_elems_2777_){
_start:
{
lean_object* v_toApplicative_2778_; lean_object* v_toBind_2779_; lean_object* v_getRef_2780_; lean_object* v_toPure_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; 
v_toApplicative_2778_ = lean_ctor_get(v_inst_2774_, 0);
lean_inc_ref(v_toApplicative_2778_);
v_toBind_2779_ = lean_ctor_get(v_inst_2774_, 1);
lean_inc(v_toBind_2779_);
lean_dec_ref(v_inst_2774_);
v_getRef_2780_ = lean_ctor_get(v_inst_2775_, 0);
lean_inc(v_getRef_2780_);
lean_dec_ref(v_inst_2775_);
v_toPure_2781_ = lean_ctor_get(v_toApplicative_2778_, 1);
lean_inc(v_toPure_2781_);
lean_dec_ref(v_toApplicative_2778_);
v___f_2782_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2782_, 0, v_elems_2777_);
lean_closure_set(v___f_2782_, 1, v_toPure_2781_);
lean_closure_set(v___f_2782_, 2, v_sep_2776_);
v___x_2783_ = lean_apply_4(v_toBind_2779_, lean_box(0), lean_box(0), v_getRef_2780_, v___f_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_sep_2787_, lean_object* v_elems_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2785_, v_inst_2786_, v_sep_2787_, v_elems_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object* v_sep_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(v___x_2791_, 0, v_sep_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2792_, lean_object* v_elems_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2792_, v_elems_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2795_, lean_object* v_elems_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2795_, v_elems_2796_);
lean_dec_ref(v_elems_2796_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2798_, lean_object* v_sep_2799_, lean_object* v_elems_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2799_, v_elems_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2802_, lean_object* v_sep_2803_, lean_object* v_elems_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2802_, v_sep_2803_, v_elems_2804_);
lean_dec_ref(v_elems_2804_);
lean_dec(v_k_2802_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2806_, lean_object* v_sep_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2808_, 0, v_k_2806_);
lean_closure_set(v___x_2808_, 1, v_sep_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = lean_array_get_size(v_x_2816_);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = lean_nat_dec_eq(v___x_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2820_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2821_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2822_ = lean_box(2);
v___x_2823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2821_);
lean_ctor_set(v___x_2823_, 2, v_x_2816_);
v___x_2824_ = lean_unsigned_to_nat(2u);
v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2824_);
v___x_2826_ = lean_array_push(v___x_2825_, v_fn_2815_);
v___x_2827_ = lean_array_push(v___x_2826_, v___x_2823_);
v___x_2828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2822_);
lean_ctor_set(v___x_2828_, 1, v___x_2820_);
lean_ctor_set(v___x_2828_, 2, v___x_2827_);
return v___x_2828_;
}
else
{
lean_dec_ref(v_x_2816_);
return v_fn_2815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2829_, lean_object* v_args_2830_){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = l_Lean_mkCIdent(v_fn_2829_);
v___x_2832_ = l_Lean_Syntax_mkApp(v___x_2831_, v_args_2830_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2833_, lean_object* v_val_2834_, lean_object* v_info_2835_){
_start:
{
lean_object* v_atom_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_atom_2836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2836_, 0, v_info_2835_);
lean_ctor_set(v_atom_2836_, 1, v_val_2834_);
v___x_2837_ = lean_unsigned_to_nat(1u);
v___x_2838_ = lean_mk_empty_array_with_capacity(v___x_2837_);
v___x_2839_ = lean_array_push(v___x_2838_, v_atom_2836_);
v___x_2840_ = lean_box(2);
v___x_2841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v_kind_2833_);
lean_ctor_set(v___x_2841_, 2, v___x_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2845_, lean_object* v_info_2846_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2848_ = l_Char_quote(v_val_2845_);
v___x_2849_ = l_Lean_Syntax_mkLit(v___x_2847_, v___x_2848_, v_info_2846_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2850_, lean_object* v_info_2851_){
_start:
{
uint32_t v_val_boxed_2852_; lean_object* v_res_2853_; 
v_val_boxed_2852_ = lean_unbox_uint32(v_val_2850_);
lean_dec(v_val_2850_);
v_res_2853_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2852_, v_info_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2857_, lean_object* v_info_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2860_ = l_String_quote(v_val_2857_);
v___x_2861_ = l_Lean_Syntax_mkLit(v___x_2859_, v___x_2860_, v_info_2858_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2865_, lean_object* v_info_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2868_ = l_Lean_Syntax_mkLit(v___x_2867_, v_val_2865_, v_info_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2869_, lean_object* v_info_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2872_ = l_Nat_reprFast(v_val_2869_);
v___x_2873_ = l_Lean_Syntax_mkLit(v___x_2871_, v___x_2872_, v_info_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2877_, lean_object* v_info_2878_){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2880_ = l_Lean_Syntax_mkLit(v___x_2879_, v_val_2877_, v_info_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2884_, lean_object* v_info_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2887_ = l_Lean_Syntax_mkLit(v___x_2886_, v_val_2884_, v_info_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2888_, lean_object* v_i_2889_, lean_object* v_val_2890_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_string_utf8_at_end(v_s_2888_, v_i_2889_);
if (v___x_2891_ == 0)
{
uint32_t v_c_2892_; uint32_t v___x_2893_; uint8_t v___x_2894_; 
v_c_2892_ = lean_string_utf8_get(v_s_2888_, v_i_2889_);
v___x_2893_ = 48;
v___x_2894_ = lean_uint32_dec_eq(v_c_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
uint32_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = 49;
v___x_2896_ = lean_uint32_dec_eq(v_c_2892_, v___x_2895_);
if (v___x_2896_ == 0)
{
uint32_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = 95;
v___x_2898_ = lean_uint32_dec_eq(v_c_2892_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_val_2890_);
lean_dec(v_i_2889_);
v___x_2899_ = lean_box(0);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_string_utf8_next(v_s_2888_, v_i_2889_);
lean_dec(v_i_2889_);
v_i_2889_ = v___x_2900_;
goto _start;
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2902_ = lean_string_utf8_next(v_s_2888_, v_i_2889_);
lean_dec(v_i_2889_);
v___x_2903_ = lean_unsigned_to_nat(2u);
v___x_2904_ = lean_nat_mul(v___x_2903_, v_val_2890_);
lean_dec(v_val_2890_);
v___x_2905_ = lean_unsigned_to_nat(1u);
v___x_2906_ = lean_nat_add(v___x_2904_, v___x_2905_);
lean_dec(v___x_2904_);
v_i_2889_ = v___x_2902_;
v_val_2890_ = v___x_2906_;
goto _start;
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_string_utf8_next(v_s_2888_, v_i_2889_);
lean_dec(v_i_2889_);
v___x_2909_ = lean_unsigned_to_nat(2u);
v___x_2910_ = lean_nat_mul(v___x_2909_, v_val_2890_);
lean_dec(v_val_2890_);
v_i_2889_ = v___x_2908_;
v_val_2890_ = v___x_2910_;
goto _start;
}
}
else
{
lean_object* v___x_2912_; 
lean_dec(v_i_2889_);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_val_2890_);
return v___x_2912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2913_, lean_object* v_i_2914_, lean_object* v_val_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2913_, v_i_2914_, v_val_2915_);
lean_dec_ref(v_s_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2917_, lean_object* v_i_2918_, lean_object* v_val_2919_){
_start:
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_string_utf8_at_end(v_s_2917_, v_i_2918_);
if (v___x_2920_ == 0)
{
uint32_t v_c_2921_; uint8_t v___y_2923_; uint32_t v___x_2937_; uint8_t v___x_2938_; 
v_c_2921_ = lean_string_utf8_get(v_s_2917_, v_i_2918_);
v___x_2937_ = 48;
v___x_2938_ = lean_uint32_dec_le(v___x_2937_, v_c_2921_);
if (v___x_2938_ == 0)
{
v___y_2923_ = v___x_2938_;
goto v___jp_2922_;
}
else
{
uint32_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = 55;
v___x_2940_ = lean_uint32_dec_le(v_c_2921_, v___x_2939_);
v___y_2923_ = v___x_2940_;
goto v___jp_2922_;
}
v___jp_2922_:
{
if (v___y_2923_ == 0)
{
uint32_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = 95;
v___x_2925_ = lean_uint32_dec_eq(v_c_2921_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v_val_2919_);
lean_dec(v_i_2918_);
v___x_2926_ = lean_box(0);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_string_utf8_next(v_s_2917_, v_i_2918_);
lean_dec(v_i_2918_);
v_i_2918_ = v___x_2927_;
goto _start;
}
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2929_ = lean_string_utf8_next(v_s_2917_, v_i_2918_);
lean_dec(v_i_2918_);
v___x_2930_ = lean_unsigned_to_nat(8u);
v___x_2931_ = lean_nat_mul(v___x_2930_, v_val_2919_);
lean_dec(v_val_2919_);
v___x_2932_ = lean_uint32_to_nat(v_c_2921_);
v___x_2933_ = lean_nat_add(v___x_2931_, v___x_2932_);
lean_dec(v___x_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_unsigned_to_nat(48u);
v___x_2935_ = lean_nat_sub(v___x_2933_, v___x_2934_);
lean_dec(v___x_2933_);
v_i_2918_ = v___x_2929_;
v_val_2919_ = v___x_2935_;
goto _start;
}
}
}
else
{
lean_object* v___x_2941_; 
lean_dec(v_i_2918_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_val_2919_);
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2942_, lean_object* v_i_2943_, lean_object* v_val_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2942_, v_i_2943_, v_val_2944_);
lean_dec_ref(v_s_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2946_, lean_object* v_i_2947_){
_start:
{
uint32_t v_c_2948_; lean_object* v_i_2949_; uint8_t v___y_2951_; uint8_t v___y_2961_; uint8_t v___y_2974_; uint32_t v___x_2984_; uint8_t v___x_2985_; 
v_c_2948_ = lean_string_utf8_get(v_s_2946_, v_i_2947_);
v_i_2949_ = lean_string_utf8_next(v_s_2946_, v_i_2947_);
v___x_2984_ = 48;
v___x_2985_ = lean_uint32_dec_le(v___x_2984_, v_c_2948_);
if (v___x_2985_ == 0)
{
v___y_2974_ = v___x_2985_;
goto v___jp_2973_;
}
else
{
uint32_t v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = 57;
v___x_2987_ = lean_uint32_dec_le(v_c_2948_, v___x_2986_);
v___y_2974_ = v___x_2987_;
goto v___jp_2973_;
}
v___jp_2950_:
{
if (v___y_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v_i_2949_);
v___x_2952_ = lean_box(0);
return v___x_2952_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2953_ = lean_unsigned_to_nat(10u);
v___x_2954_ = lean_uint32_to_nat(v_c_2948_);
v___x_2955_ = lean_nat_add(v___x_2953_, v___x_2954_);
lean_dec(v___x_2954_);
v___x_2956_ = lean_unsigned_to_nat(65u);
v___x_2957_ = lean_nat_sub(v___x_2955_, v___x_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v_i_2949_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
v___jp_2960_:
{
if (v___y_2961_ == 0)
{
uint32_t v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = 65;
v___x_2963_ = lean_uint32_dec_le(v___x_2962_, v_c_2948_);
if (v___x_2963_ == 0)
{
v___y_2951_ = v___x_2963_;
goto v___jp_2950_;
}
else
{
uint32_t v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = 70;
v___x_2965_ = lean_uint32_dec_le(v_c_2948_, v___x_2964_);
v___y_2951_ = v___x_2965_;
goto v___jp_2950_;
}
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2966_ = lean_unsigned_to_nat(10u);
v___x_2967_ = lean_uint32_to_nat(v_c_2948_);
v___x_2968_ = lean_nat_add(v___x_2966_, v___x_2967_);
lean_dec(v___x_2967_);
v___x_2969_ = lean_unsigned_to_nat(97u);
v___x_2970_ = lean_nat_sub(v___x_2968_, v___x_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
lean_ctor_set(v___x_2971_, 1, v_i_2949_);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
v___jp_2973_:
{
if (v___y_2974_ == 0)
{
uint32_t v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = 97;
v___x_2976_ = lean_uint32_dec_le(v___x_2975_, v_c_2948_);
if (v___x_2976_ == 0)
{
v___y_2961_ = v___x_2976_;
goto v___jp_2960_;
}
else
{
uint32_t v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = 102;
v___x_2978_ = lean_uint32_dec_le(v_c_2948_, v___x_2977_);
v___y_2961_ = v___x_2978_;
goto v___jp_2960_;
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2979_ = lean_uint32_to_nat(v_c_2948_);
v___x_2980_ = lean_unsigned_to_nat(48u);
v___x_2981_ = lean_nat_sub(v___x_2979_, v___x_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v_i_2949_);
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2988_, lean_object* v_i_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2988_, v_i_2989_);
lean_dec(v_i_2989_);
lean_dec_ref(v_s_2988_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2991_, lean_object* v_i_2992_, lean_object* v_val_2993_){
_start:
{
uint8_t v___x_2994_; 
v___x_2994_ = lean_string_utf8_at_end(v_s_2991_, v_i_2992_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2991_, v_i_2992_);
if (lean_obj_tag(v___x_2995_) == 0)
{
uint32_t v___x_2996_; uint32_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = lean_string_utf8_get(v_s_2991_, v_i_2992_);
v___x_2997_ = 95;
v___x_2998_ = lean_uint32_dec_eq(v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_dec(v_val_2993_);
lean_dec(v_i_2992_);
v___x_2999_ = lean_box(0);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_string_utf8_next(v_s_2991_, v_i_2992_);
lean_dec(v_i_2992_);
v_i_2992_ = v___x_3000_;
goto _start;
}
}
else
{
lean_object* v_val_3002_; lean_object* v_fst_3003_; lean_object* v_snd_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec(v_i_2992_);
v_val_3002_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_3002_);
lean_dec_ref(v___x_2995_);
v_fst_3003_ = lean_ctor_get(v_val_3002_, 0);
lean_inc(v_fst_3003_);
v_snd_3004_ = lean_ctor_get(v_val_3002_, 1);
lean_inc(v_snd_3004_);
lean_dec(v_val_3002_);
v___x_3005_ = lean_unsigned_to_nat(16u);
v___x_3006_ = lean_nat_mul(v___x_3005_, v_val_2993_);
lean_dec(v_val_2993_);
v___x_3007_ = lean_nat_add(v___x_3006_, v_fst_3003_);
lean_dec(v_fst_3003_);
lean_dec(v___x_3006_);
v_i_2992_ = v_snd_3004_;
v_val_2993_ = v___x_3007_;
goto _start;
}
}
else
{
lean_object* v___x_3009_; 
lean_dec(v_i_2992_);
v___x_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_val_2993_);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3010_, lean_object* v_i_3011_, lean_object* v_val_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3010_, v_i_3011_, v_val_3012_);
lean_dec_ref(v_s_3010_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3014_, lean_object* v_i_3015_, lean_object* v_val_3016_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_string_utf8_at_end(v_s_3014_, v_i_3015_);
if (v___x_3017_ == 0)
{
uint32_t v_c_3018_; uint8_t v___y_3020_; uint32_t v___x_3034_; uint8_t v___x_3035_; 
v_c_3018_ = lean_string_utf8_get(v_s_3014_, v_i_3015_);
v___x_3034_ = 48;
v___x_3035_ = lean_uint32_dec_le(v___x_3034_, v_c_3018_);
if (v___x_3035_ == 0)
{
v___y_3020_ = v___x_3035_;
goto v___jp_3019_;
}
else
{
uint32_t v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = 57;
v___x_3037_ = lean_uint32_dec_le(v_c_3018_, v___x_3036_);
v___y_3020_ = v___x_3037_;
goto v___jp_3019_;
}
v___jp_3019_:
{
if (v___y_3020_ == 0)
{
uint32_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = 95;
v___x_3022_ = lean_uint32_dec_eq(v_c_3018_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
lean_dec(v_val_3016_);
lean_dec(v_i_3015_);
v___x_3023_ = lean_box(0);
return v___x_3023_;
}
else
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_string_utf8_next(v_s_3014_, v_i_3015_);
lean_dec(v_i_3015_);
v_i_3015_ = v___x_3024_;
goto _start;
}
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3026_ = lean_string_utf8_next(v_s_3014_, v_i_3015_);
lean_dec(v_i_3015_);
v___x_3027_ = lean_unsigned_to_nat(10u);
v___x_3028_ = lean_nat_mul(v___x_3027_, v_val_3016_);
lean_dec(v_val_3016_);
v___x_3029_ = lean_uint32_to_nat(v_c_3018_);
v___x_3030_ = lean_nat_add(v___x_3028_, v___x_3029_);
lean_dec(v___x_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_unsigned_to_nat(48u);
v___x_3032_ = lean_nat_sub(v___x_3030_, v___x_3031_);
lean_dec(v___x_3030_);
v_i_3015_ = v___x_3026_;
v_val_3016_ = v___x_3032_;
goto _start;
}
}
}
else
{
lean_object* v___x_3038_; 
lean_dec(v_i_3015_);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_val_3016_);
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3039_, lean_object* v_i_3040_, lean_object* v_val_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3039_, v_i_3040_, v_val_3041_);
lean_dec_ref(v_s_3039_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3045_){
_start:
{
lean_object* v_len_3046_; lean_object* v___x_3047_; uint8_t v___y_3049_; uint8_t v___y_3062_; uint8_t v___x_3065_; 
v_len_3046_ = lean_string_length(v_s_3045_);
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3065_ = lean_nat_dec_eq(v_len_3046_, v___x_3047_);
if (v___x_3065_ == 0)
{
uint32_t v_c_3066_; uint32_t v___x_3067_; uint8_t v___x_3068_; 
v_c_3066_ = lean_string_utf8_get(v_s_3045_, v___x_3047_);
v___x_3067_ = 48;
v___x_3068_ = lean_uint32_dec_eq(v_c_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
uint8_t v___x_3069_; 
lean_dec(v_len_3046_);
v___x_3069_ = lean_uint32_dec_le(v___x_3067_, v_c_3066_);
if (v___x_3069_ == 0)
{
v___y_3062_ = v___x_3069_;
goto v___jp_3061_;
}
else
{
uint32_t v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = 57;
v___x_3071_ = lean_uint32_dec_le(v_c_3066_, v___x_3070_);
v___y_3062_ = v___x_3071_;
goto v___jp_3061_;
}
}
else
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_dec_eq(v_len_3046_, v___x_3072_);
lean_dec(v_len_3046_);
if (v___x_3073_ == 0)
{
uint32_t v_c_3074_; uint32_t v___x_3075_; uint8_t v___x_3076_; 
v_c_3074_ = lean_string_utf8_get(v_s_3045_, v___x_3072_);
v___x_3075_ = 120;
v___x_3076_ = lean_uint32_dec_eq(v_c_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 88;
v___x_3078_ = lean_uint32_dec_eq(v_c_3074_, v___x_3077_);
if (v___x_3078_ == 0)
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 98;
v___x_3080_ = lean_uint32_dec_eq(v_c_3074_, v___x_3079_);
if (v___x_3080_ == 0)
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 66;
v___x_3082_ = lean_uint32_dec_eq(v_c_3074_, v___x_3081_);
if (v___x_3082_ == 0)
{
uint32_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = 111;
v___x_3084_ = lean_uint32_dec_eq(v_c_3074_, v___x_3083_);
if (v___x_3084_ == 0)
{
uint32_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = 79;
v___x_3086_ = lean_uint32_dec_eq(v_c_3074_, v___x_3085_);
if (v___x_3086_ == 0)
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_uint32_dec_le(v___x_3067_, v_c_3074_);
if (v___x_3087_ == 0)
{
v___y_3049_ = v___x_3087_;
goto v___jp_3048_;
}
else
{
uint32_t v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = 57;
v___x_3089_ = lean_uint32_dec_le(v_c_3074_, v___x_3088_);
v___y_3049_ = v___x_3089_;
goto v___jp_3048_;
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
goto v___jp_3058_;
}
}
else
{
goto v___jp_3058_;
}
}
else
{
lean_object* v___x_3090_; 
v___x_3090_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3090_;
}
}
}
else
{
lean_object* v___x_3091_; 
lean_dec(v_len_3046_);
v___x_3091_ = lean_box(0);
return v___x_3091_;
}
v___jp_3048_:
{
if (v___y_3049_ == 0)
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_box(0);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3045_, v___x_3047_, v___x_3047_);
return v___x_3051_;
}
}
v___jp_3052_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_unsigned_to_nat(2u);
v___x_3054_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3045_, v___x_3053_, v___x_3047_);
return v___x_3054_;
}
v___jp_3055_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(2u);
v___x_3057_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3045_, v___x_3056_, v___x_3047_);
return v___x_3057_;
}
v___jp_3058_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_unsigned_to_nat(2u);
v___x_3060_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3045_, v___x_3059_, v___x_3047_);
return v___x_3060_;
}
v___jp_3061_:
{
if (v___y_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3045_, v___x_3047_, v___x_3047_);
return v___x_3064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3092_);
lean_dec_ref(v_s_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3094_, lean_object* v_stx_3095_){
_start:
{
if (lean_obj_tag(v_stx_3095_) == 1)
{
lean_object* v_kind_3096_; lean_object* v_args_3097_; uint8_t v___x_3098_; 
v_kind_3096_ = lean_ctor_get(v_stx_3095_, 1);
v_args_3097_ = lean_ctor_get(v_stx_3095_, 2);
v___x_3098_ = lean_name_eq(v_kind_3096_, v_litKind_3094_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = lean_array_get_size(v_args_3097_);
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_dec_eq(v___x_3100_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_box(0);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = lean_array_fget_borrowed(v_args_3097_, v___x_3104_);
if (lean_obj_tag(v___x_3105_) == 2)
{
lean_object* v_val_3106_; lean_object* v___x_3107_; 
v_val_3106_ = lean_ctor_get(v___x_3105_, 1);
lean_inc_ref(v_val_3106_);
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v_val_3106_);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_box(0);
return v___x_3108_;
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
lean_dec_ref(v___x_3115_);
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
v___y_3144_ = v___x_3159_;
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
v___y_3220_ = v___x_3241_;
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
v___y_3263_ = v___x_3287_;
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
lean_object* v_len_3296_; lean_object* v___x_3297_; uint8_t v___y_3299_; uint8_t v___x_3302_; 
v_len_3296_ = lean_string_length(v_s_3295_);
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3302_ = lean_nat_dec_eq(v_len_3296_, v___x_3297_);
lean_dec(v_len_3296_);
if (v___x_3302_ == 0)
{
uint32_t v_c_3303_; uint32_t v___x_3304_; uint8_t v___x_3305_; 
v_c_3303_ = lean_string_utf8_get(v_s_3295_, v___x_3297_);
v___x_3304_ = 48;
v___x_3305_ = lean_uint32_dec_le(v___x_3304_, v_c_3303_);
if (v___x_3305_ == 0)
{
v___y_3299_ = v___x_3305_;
goto v___jp_3298_;
}
else
{
uint32_t v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = 57;
v___x_3307_ = lean_uint32_dec_le(v_c_3303_, v___x_3306_);
v___y_3299_ = v___x_3307_;
goto v___jp_3298_;
}
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_box(0);
return v___x_3308_;
}
v___jp_3298_:
{
if (v___y_3299_ == 0)
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_box(0);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3295_, v___x_3297_, v___x_3297_);
return v___x_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3309_);
lean_dec_ref(v_s_3309_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3311_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3313_ = l_Lean_Syntax_isLit_x3f(v___x_3312_, v_stx_3311_);
if (lean_obj_tag(v___x_3313_) == 1)
{
lean_object* v_val_3314_; lean_object* v___x_3315_; 
v_val_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_val_3314_);
lean_dec_ref(v___x_3313_);
v___x_3315_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3314_);
lean_dec(v_val_3314_);
return v___x_3315_;
}
else
{
lean_object* v___x_3316_; 
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
return v___x_3316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3317_);
lean_dec(v_stx_3317_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3319_){
_start:
{
switch(lean_obj_tag(v_x_3319_))
{
case 2:
{
lean_object* v_val_3320_; lean_object* v___x_3321_; 
v_val_3320_ = lean_ctor_get(v_x_3319_, 1);
lean_inc_ref(v_val_3320_);
lean_dec_ref(v_x_3319_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_val_3320_);
return v___x_3321_;
}
case 3:
{
lean_object* v_rawVal_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_rawVal_3322_ = lean_ctor_get(v_x_3319_, 1);
lean_inc_ref(v_rawVal_3322_);
lean_dec_ref(v_x_3319_);
v___x_3323_ = lean_substring_tostring(v_rawVal_3322_);
v___x_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
default: 
{
lean_object* v___x_3325_; 
lean_dec(v_x_3319_);
v___x_3325_ = lean_box(0);
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3326_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_unsigned_to_nat(0u);
return v___x_3328_;
}
else
{
lean_object* v_val_3329_; 
v_val_3329_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3329_);
lean_dec_ref(v___x_3327_);
return v_val_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Syntax_toNat(v_stx_3330_);
lean_dec(v_stx_3330_);
return v_res_3331_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = 9;
v___x_3333_ = lean_box_uint32(v___x_3332_);
return v___x_3333_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = 10;
v___x_3335_ = lean_box_uint32(v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = 13;
v___x_3337_ = lean_box_uint32(v___x_3336_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = 39;
v___x_3339_ = lean_box_uint32(v___x_3338_);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = 34;
v___x_3341_ = lean_box_uint32(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = 92;
v___x_3343_ = lean_box_uint32(v___x_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3344_, lean_object* v_i_3345_){
_start:
{
uint32_t v_c_3346_; lean_object* v_i_3347_; uint32_t v___x_3348_; uint8_t v___x_3349_; 
v_c_3346_ = lean_string_utf8_get(v_s_3344_, v_i_3345_);
v_i_3347_ = lean_string_utf8_next(v_s_3344_, v_i_3345_);
v___x_3348_ = 92;
v___x_3349_ = lean_uint32_dec_eq(v_c_3346_, v___x_3348_);
if (v___x_3349_ == 0)
{
uint32_t v___x_3350_; uint8_t v___x_3351_; 
v___x_3350_ = 34;
v___x_3351_ = lean_uint32_dec_eq(v_c_3346_, v___x_3350_);
if (v___x_3351_ == 0)
{
uint32_t v___x_3352_; uint8_t v___x_3353_; 
v___x_3352_ = 39;
v___x_3353_ = lean_uint32_dec_eq(v_c_3346_, v___x_3352_);
if (v___x_3353_ == 0)
{
uint32_t v___x_3354_; uint8_t v___x_3355_; 
v___x_3354_ = 114;
v___x_3355_ = lean_uint32_dec_eq(v_c_3346_, v___x_3354_);
if (v___x_3355_ == 0)
{
uint32_t v___x_3356_; uint8_t v___x_3357_; 
v___x_3356_ = 110;
v___x_3357_ = lean_uint32_dec_eq(v_c_3346_, v___x_3356_);
if (v___x_3357_ == 0)
{
uint32_t v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = 116;
v___x_3359_ = lean_uint32_dec_eq(v_c_3346_, v___x_3358_);
if (v___x_3359_ == 0)
{
uint32_t v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = 120;
v___x_3361_ = lean_uint32_dec_eq(v_c_3346_, v___x_3360_);
if (v___x_3361_ == 0)
{
uint32_t v___x_3362_; uint8_t v___x_3363_; 
v___x_3362_ = 117;
v___x_3363_ = lean_uint32_dec_eq(v_c_3346_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec(v_i_3347_);
v___x_3364_ = lean_box(0);
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3344_, v_i_3347_);
lean_dec(v_i_3347_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_box(0);
return v___x_3366_;
}
else
{
lean_object* v_val_3367_; lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3370_; 
v_val_3367_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3367_);
lean_dec_ref(v___x_3365_);
v_fst_3368_ = lean_ctor_get(v_val_3367_, 0);
lean_inc(v_fst_3368_);
v_snd_3369_ = lean_ctor_get(v_val_3367_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_val_3367_);
v___x_3370_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3344_, v_snd_3369_);
lean_dec(v_snd_3369_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v___x_3371_; 
lean_dec(v_fst_3368_);
v___x_3371_ = lean_box(0);
return v___x_3371_;
}
else
{
lean_object* v_val_3372_; lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3375_; 
v_val_3372_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_val_3372_);
lean_dec_ref(v___x_3370_);
v_fst_3373_ = lean_ctor_get(v_val_3372_, 0);
lean_inc(v_fst_3373_);
v_snd_3374_ = lean_ctor_get(v_val_3372_, 1);
lean_inc(v_snd_3374_);
lean_dec(v_val_3372_);
v___x_3375_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3344_, v_snd_3374_);
lean_dec(v_snd_3374_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; 
lean_dec(v_fst_3373_);
lean_dec(v_fst_3368_);
v___x_3376_ = lean_box(0);
return v___x_3376_;
}
else
{
lean_object* v_val_3377_; lean_object* v_fst_3378_; lean_object* v_snd_3379_; lean_object* v___x_3380_; 
v_val_3377_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_val_3377_);
lean_dec_ref(v___x_3375_);
v_fst_3378_ = lean_ctor_get(v_val_3377_, 0);
lean_inc(v_fst_3378_);
v_snd_3379_ = lean_ctor_get(v_val_3377_, 1);
lean_inc(v_snd_3379_);
lean_dec(v_val_3377_);
v___x_3380_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3344_, v_snd_3379_);
lean_dec(v_snd_3379_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3381_; 
lean_dec(v_fst_3378_);
lean_dec(v_fst_3373_);
lean_dec(v_fst_3368_);
v___x_3381_ = lean_box(0);
return v___x_3381_;
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3407_; 
v_val_3382_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3384_ = v___x_3380_;
v_isShared_3385_ = v_isSharedCheck_3407_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_val_3382_);
lean_dec(v___x_3380_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3407_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_fst_3386_; lean_object* v_snd_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3406_; 
v_fst_3386_ = lean_ctor_get(v_val_3382_, 0);
v_snd_3387_ = lean_ctor_get(v_val_3382_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_val_3382_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3389_ = v_val_3382_;
v_isShared_3390_ = v_isSharedCheck_3406_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_snd_3387_);
lean_inc(v_fst_3386_);
lean_dec(v_val_3382_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3406_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; uint32_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3391_ = lean_unsigned_to_nat(16u);
v___x_3392_ = lean_nat_mul(v___x_3391_, v_fst_3368_);
lean_dec(v_fst_3368_);
v___x_3393_ = lean_nat_add(v___x_3392_, v_fst_3373_);
lean_dec(v_fst_3373_);
lean_dec(v___x_3392_);
v___x_3394_ = lean_nat_mul(v___x_3391_, v___x_3393_);
lean_dec(v___x_3393_);
v___x_3395_ = lean_nat_add(v___x_3394_, v_fst_3378_);
lean_dec(v_fst_3378_);
lean_dec(v___x_3394_);
v___x_3396_ = lean_nat_mul(v___x_3391_, v___x_3395_);
lean_dec(v___x_3395_);
v___x_3397_ = lean_nat_add(v___x_3396_, v_fst_3386_);
lean_dec(v_fst_3386_);
lean_dec(v___x_3396_);
v___x_3398_ = l_Char_ofNat(v___x_3397_);
lean_dec(v___x_3397_);
v___x_3399_ = lean_box_uint32(v___x_3398_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3399_);
v___x_3401_ = v___x_3389_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_snd_3387_);
v___x_3401_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3401_);
v___x_3403_ = v___x_3384_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
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
lean_object* v___x_3408_; 
v___x_3408_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3344_, v_i_3347_);
lean_dec(v_i_3347_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_box(0);
return v___x_3409_;
}
else
{
lean_object* v_val_3410_; lean_object* v_fst_3411_; lean_object* v_snd_3412_; lean_object* v___x_3413_; 
v_val_3410_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_val_3410_);
lean_dec_ref(v___x_3408_);
v_fst_3411_ = lean_ctor_get(v_val_3410_, 0);
lean_inc(v_fst_3411_);
v_snd_3412_ = lean_ctor_get(v_val_3410_, 1);
lean_inc(v_snd_3412_);
lean_dec(v_val_3410_);
v___x_3413_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3344_, v_snd_3412_);
lean_dec(v_snd_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3414_; 
lean_dec(v_fst_3411_);
v___x_3414_ = lean_box(0);
return v___x_3414_;
}
else
{
lean_object* v_val_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3436_; 
v_val_3415_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3436_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_val_3415_);
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3436_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3435_; 
v_fst_3419_ = lean_ctor_get(v_val_3415_, 0);
v_snd_3420_ = lean_ctor_get(v_val_3415_, 1);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_val_3415_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3422_ = v_val_3415_;
v_isShared_3423_ = v_isSharedCheck_3435_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_snd_3420_);
lean_inc(v_fst_3419_);
lean_dec(v_val_3415_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3435_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint32_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3424_ = lean_unsigned_to_nat(16u);
v___x_3425_ = lean_nat_mul(v___x_3424_, v_fst_3411_);
lean_dec(v_fst_3411_);
v___x_3426_ = lean_nat_add(v___x_3425_, v_fst_3419_);
lean_dec(v_fst_3419_);
lean_dec(v___x_3425_);
v___x_3427_ = l_Char_ofNat(v___x_3426_);
lean_dec(v___x_3426_);
v___x_3428_ = lean_box_uint32(v___x_3427_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3428_);
v___x_3430_ = v___x_3422_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_snd_3420_);
v___x_3430_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3432_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3430_);
v___x_3432_ = v___x_3417_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
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
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v_i_3347_);
v___x_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v_i_3347_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
return v___x_3442_;
}
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v_i_3347_);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v_i_3347_);
v___x_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v_i_3347_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v_i_3347_);
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
return v___x_3454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3455_, lean_object* v_i_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Syntax_decodeQuotedChar(v_s_3455_, v_i_3456_);
lean_dec(v_i_3456_);
lean_dec_ref(v_s_3455_);
return v_res_3457_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3458_){
_start:
{
uint8_t v___y_3460_; uint32_t v___x_3465_; uint8_t v___x_3466_; 
v___x_3465_ = 32;
v___x_3466_ = lean_uint32_dec_eq(v___y_3458_, v___x_3465_);
if (v___x_3466_ == 0)
{
uint32_t v___x_3467_; uint8_t v___x_3468_; 
v___x_3467_ = 9;
v___x_3468_ = lean_uint32_dec_eq(v___y_3458_, v___x_3467_);
v___y_3460_ = v___x_3468_;
goto v___jp_3459_;
}
else
{
v___y_3460_ = v___x_3466_;
goto v___jp_3459_;
}
v___jp_3459_:
{
if (v___y_3460_ == 0)
{
uint32_t v___x_3461_; uint8_t v___x_3462_; 
v___x_3461_ = 13;
v___x_3462_ = lean_uint32_dec_eq(v___y_3458_, v___x_3461_);
if (v___x_3462_ == 0)
{
uint32_t v___x_3463_; uint8_t v___x_3464_; 
v___x_3463_ = 10;
v___x_3464_ = lean_uint32_dec_eq(v___y_3458_, v___x_3463_);
return v___x_3464_;
}
else
{
return v___x_3462_;
}
}
else
{
return v___y_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3469_){
_start:
{
uint32_t v___y_233__boxed_3470_; uint8_t v_res_3471_; lean_object* v_r_3472_; 
v___y_233__boxed_3470_ = lean_unbox_uint32(v___y_3469_);
lean_dec(v___y_3469_);
v_res_3471_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_233__boxed_3470_);
v_r_3472_ = lean_box(v_res_3471_);
return v_r_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3474_, lean_object* v_i_3475_){
_start:
{
lean_object* v___f_3476_; uint8_t v___y_3482_; uint32_t v___x_3484_; uint8_t v___y_3486_; uint32_t v___x_3491_; uint8_t v___x_3492_; 
v___f_3476_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3484_ = lean_string_utf8_get(v_s_3474_, v_i_3475_);
v___x_3491_ = 32;
v___x_3492_ = lean_uint32_dec_eq(v___x_3484_, v___x_3491_);
if (v___x_3492_ == 0)
{
uint32_t v___x_3493_; uint8_t v___x_3494_; 
v___x_3493_ = 9;
v___x_3494_ = lean_uint32_dec_eq(v___x_3484_, v___x_3493_);
v___y_3486_ = v___x_3494_;
goto v___jp_3485_;
}
else
{
v___y_3486_ = v___x_3492_;
goto v___jp_3485_;
}
v___jp_3477_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = lean_string_utf8_next(v_s_3474_, v_i_3475_);
v___x_3479_ = lean_string_nextwhile(v_s_3474_, v___f_3476_, v___x_3478_);
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
return v___x_3480_;
}
v___jp_3481_:
{
if (v___y_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref(v_s_3474_);
v___x_3483_ = lean_box(0);
return v___x_3483_;
}
else
{
goto v___jp_3477_;
}
}
v___jp_3485_:
{
if (v___y_3486_ == 0)
{
uint32_t v___x_3487_; uint8_t v___x_3488_; 
v___x_3487_ = 13;
v___x_3488_ = lean_uint32_dec_eq(v___x_3484_, v___x_3487_);
if (v___x_3488_ == 0)
{
uint32_t v___x_3489_; uint8_t v___x_3490_; 
v___x_3489_ = 10;
v___x_3490_ = lean_uint32_dec_eq(v___x_3484_, v___x_3489_);
v___y_3482_ = v___x_3490_;
goto v___jp_3481_;
}
else
{
v___y_3482_ = v___x_3488_;
goto v___jp_3481_;
}
}
else
{
goto v___jp_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3495_, lean_object* v_i_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Syntax_decodeStringGap(v_s_3495_, v_i_3496_);
lean_dec(v_i_3496_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3498_, lean_object* v_i_3499_, lean_object* v_acc_3500_){
_start:
{
uint32_t v_c_3501_; uint32_t v___x_3502_; uint8_t v___x_3503_; 
v_c_3501_ = lean_string_utf8_get(v_s_3498_, v_i_3499_);
v___x_3502_ = 34;
v___x_3503_ = lean_uint32_dec_eq(v_c_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v_i_3504_; uint8_t v___x_3505_; 
v_i_3504_ = lean_string_utf8_next(v_s_3498_, v_i_3499_);
lean_dec(v_i_3499_);
v___x_3505_ = lean_string_utf8_at_end(v_s_3498_, v_i_3504_);
if (v___x_3505_ == 0)
{
uint32_t v___x_3506_; uint8_t v___x_3507_; 
v___x_3506_ = 92;
v___x_3507_ = lean_uint32_dec_eq(v_c_3501_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_string_push(v_acc_3500_, v_c_3501_);
v_i_3499_ = v_i_3504_;
v_acc_3500_ = v___x_3508_;
goto _start;
}
else
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_Syntax_decodeQuotedChar(v_s_3498_, v_i_3504_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; lean_object* v_fst_3512_; lean_object* v_snd_3513_; uint32_t v___x_3514_; lean_object* v___x_3515_; 
lean_dec(v_i_3504_);
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3511_);
lean_dec_ref(v___x_3510_);
v_fst_3512_ = lean_ctor_get(v_val_3511_, 0);
lean_inc(v_fst_3512_);
v_snd_3513_ = lean_ctor_get(v_val_3511_, 1);
lean_inc(v_snd_3513_);
lean_dec(v_val_3511_);
v___x_3514_ = lean_unbox_uint32(v_fst_3512_);
lean_dec(v_fst_3512_);
v___x_3515_ = lean_string_push(v_acc_3500_, v___x_3514_);
v_i_3499_ = v_snd_3513_;
v_acc_3500_ = v___x_3515_;
goto _start;
}
else
{
lean_object* v___x_3517_; 
lean_dec(v___x_3510_);
lean_inc_ref(v_s_3498_);
v___x_3517_ = l_Lean_Syntax_decodeStringGap(v_s_3498_, v_i_3504_);
lean_dec(v_i_3504_);
if (lean_obj_tag(v___x_3517_) == 1)
{
lean_object* v_val_3518_; 
v_val_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_val_3518_);
lean_dec_ref(v___x_3517_);
v_i_3499_ = v_val_3518_;
goto _start;
}
else
{
lean_object* v___x_3520_; 
lean_dec(v___x_3517_);
lean_dec_ref(v_acc_3500_);
lean_dec_ref(v_s_3498_);
v___x_3520_ = lean_box(0);
return v___x_3520_;
}
}
}
}
else
{
lean_object* v___x_3521_; 
lean_dec(v_i_3504_);
lean_dec_ref(v_acc_3500_);
lean_dec_ref(v_s_3498_);
v___x_3521_ = lean_box(0);
return v___x_3521_;
}
}
else
{
lean_object* v___x_3522_; 
lean_dec(v_i_3499_);
lean_dec_ref(v_s_3498_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_acc_3500_);
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3523_, lean_object* v_i_3524_, lean_object* v_num_3525_){
_start:
{
uint32_t v_c_3526_; lean_object* v_i_3527_; uint32_t v___x_3528_; uint8_t v___x_3529_; 
v_c_3526_ = lean_string_utf8_get(v_s_3523_, v_i_3524_);
v_i_3527_ = lean_string_utf8_next(v_s_3523_, v_i_3524_);
lean_dec(v_i_3524_);
v___x_3528_ = 35;
v___x_3529_ = lean_uint32_dec_eq(v_c_3526_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3530_ = lean_string_utf8_byte_size(v_s_3523_);
v___x_3531_ = lean_unsigned_to_nat(1u);
v___x_3532_ = lean_nat_add(v_num_3525_, v___x_3531_);
lean_dec(v_num_3525_);
v___x_3533_ = lean_nat_sub(v___x_3530_, v___x_3532_);
lean_dec(v___x_3532_);
v___x_3534_ = lean_string_utf8_extract(v_s_3523_, v_i_3527_, v___x_3533_);
lean_dec(v___x_3533_);
lean_dec(v_i_3527_);
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
v___x_3536_ = lean_nat_add(v_num_3525_, v___x_3535_);
lean_dec(v_num_3525_);
v_i_3524_ = v_i_3527_;
v_num_3525_ = v___x_3536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3538_, lean_object* v_i_3539_, lean_object* v_num_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3538_, v_i_3539_, v_num_3540_);
lean_dec_ref(v_s_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3542_){
_start:
{
lean_object* v___x_3543_; uint32_t v___x_3544_; uint32_t v___x_3545_; uint8_t v___x_3546_; 
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_string_utf8_get(v_s_3542_, v___x_3543_);
v___x_3545_ = 114;
v___x_3546_ = lean_uint32_dec_eq(v___x_3544_, v___x_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3549_ = l_Lean_Syntax_decodeStrLitAux(v_s_3542_, v___x_3547_, v___x_3548_);
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_unsigned_to_nat(1u);
v___x_3551_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3542_, v___x_3550_, v___x_3543_);
lean_dec_ref(v_s_3542_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3553_){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3555_ = l_Lean_Syntax_isLit_x3f(v___x_3554_, v_stx_3553_);
if (lean_obj_tag(v___x_3555_) == 1)
{
lean_object* v_val_3556_; lean_object* v___x_3557_; 
v_val_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_val_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = l_Lean_Syntax_decodeStrLit(v_val_3556_);
return v___x_3557_;
}
else
{
lean_object* v___x_3558_; 
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3559_);
lean_dec(v_stx_3559_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3561_){
_start:
{
lean_object* v___x_3562_; uint32_t v_c_3563_; uint32_t v___x_3564_; uint8_t v___x_3565_; 
v___x_3562_ = lean_unsigned_to_nat(1u);
v_c_3563_ = lean_string_utf8_get(v_s_3561_, v___x_3562_);
v___x_3564_ = 92;
v___x_3565_ = lean_uint32_dec_eq(v_c_3563_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = lean_box_uint32(v_c_3563_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_unsigned_to_nat(2u);
v___x_3569_ = l_Lean_Syntax_decodeQuotedChar(v_s_3561_, v___x_3568_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_box(0);
return v___x_3570_;
}
else
{
lean_object* v_val_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3579_; 
v_val_3571_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3573_ = v___x_3569_;
v_isShared_3574_ = v_isSharedCheck_3579_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_val_3571_);
lean_dec(v___x_3569_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3579_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_fst_3575_; lean_object* v___x_3577_; 
v_fst_3575_ = lean_ctor_get(v_val_3571_, 0);
lean_inc(v_fst_3575_);
lean_dec(v_val_3571_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v_fst_3575_);
v___x_3577_ = v___x_3573_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_fst_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Syntax_decodeCharLit(v_s_3580_);
lean_dec_ref(v_s_3580_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3584_ = l_Lean_Syntax_isLit_x3f(v___x_3583_, v_stx_3582_);
if (lean_obj_tag(v___x_3584_) == 1)
{
lean_object* v_val_3585_; lean_object* v___x_3586_; 
v_val_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_val_3585_);
lean_dec_ref(v___x_3584_);
v___x_3586_ = l_Lean_Syntax_decodeCharLit(v_val_3585_);
lean_dec(v_val_3585_);
return v___x_3586_;
}
else
{
lean_object* v___x_3587_; 
lean_dec(v___x_3584_);
v___x_3587_ = lean_box(0);
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3588_);
lean_dec(v_stx_3588_);
return v_res_3589_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3590_){
_start:
{
uint8_t v___y_3592_; uint8_t v___y_3604_; uint32_t v___x_3614_; uint8_t v___x_3615_; 
v___x_3614_ = 65;
v___x_3615_ = lean_uint32_dec_le(v___x_3614_, v___y_3590_);
if (v___x_3615_ == 0)
{
goto v___jp_3609_;
}
else
{
uint32_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = 90;
v___x_3617_ = lean_uint32_dec_le(v___y_3590_, v___x_3616_);
if (v___x_3617_ == 0)
{
goto v___jp_3609_;
}
else
{
return v___x_3617_;
}
}
v___jp_3591_:
{
if (v___y_3592_ == 0)
{
uint32_t v___x_3593_; uint8_t v___x_3594_; 
v___x_3593_ = 95;
v___x_3594_ = lean_uint32_dec_eq(v___y_3590_, v___x_3593_);
if (v___x_3594_ == 0)
{
uint32_t v___x_3595_; uint8_t v___x_3596_; 
v___x_3595_ = 39;
v___x_3596_ = lean_uint32_dec_eq(v___y_3590_, v___x_3595_);
if (v___x_3596_ == 0)
{
uint32_t v___x_3597_; uint8_t v___x_3598_; 
v___x_3597_ = 33;
v___x_3598_ = lean_uint32_dec_eq(v___y_3590_, v___x_3597_);
if (v___x_3598_ == 0)
{
uint32_t v___x_3599_; uint8_t v___x_3600_; 
v___x_3599_ = 63;
v___x_3600_ = lean_uint32_dec_eq(v___y_3590_, v___x_3599_);
if (v___x_3600_ == 0)
{
uint8_t v___x_3601_; 
v___x_3601_ = l_Lean_isLetterLike(v___y_3590_);
if (v___x_3601_ == 0)
{
uint8_t v___x_3602_; 
v___x_3602_ = l_Lean_isSubScriptAlnum(v___y_3590_);
return v___x_3602_;
}
else
{
return v___x_3601_;
}
}
else
{
return v___x_3600_;
}
}
else
{
return v___x_3598_;
}
}
else
{
return v___x_3596_;
}
}
else
{
return v___x_3594_;
}
}
else
{
return v___y_3592_;
}
}
v___jp_3603_:
{
if (v___y_3604_ == 0)
{
uint32_t v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = 48;
v___x_3606_ = lean_uint32_dec_le(v___x_3605_, v___y_3590_);
if (v___x_3606_ == 0)
{
v___y_3592_ = v___x_3606_;
goto v___jp_3591_;
}
else
{
uint32_t v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = 57;
v___x_3608_ = lean_uint32_dec_le(v___y_3590_, v___x_3607_);
v___y_3592_ = v___x_3608_;
goto v___jp_3591_;
}
}
else
{
return v___y_3604_;
}
}
v___jp_3609_:
{
uint32_t v___x_3610_; uint8_t v___x_3611_; 
v___x_3610_ = 97;
v___x_3611_ = lean_uint32_dec_le(v___x_3610_, v___y_3590_);
if (v___x_3611_ == 0)
{
v___y_3604_ = v___x_3611_;
goto v___jp_3603_;
}
else
{
uint32_t v___x_3612_; uint8_t v___x_3613_; 
v___x_3612_ = 122;
v___x_3613_ = lean_uint32_dec_le(v___y_3590_, v___x_3612_);
v___y_3604_ = v___x_3613_;
goto v___jp_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3618_){
_start:
{
uint32_t v___y_1135__boxed_3619_; uint8_t v_res_3620_; lean_object* v_r_3621_; 
v___y_1135__boxed_3619_ = lean_unbox_uint32(v___y_3618_);
lean_dec(v___y_3618_);
v_res_3620_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_1135__boxed_3619_);
v_r_3621_ = lean_box(v_res_3620_);
return v_r_3621_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___y_3622_){
_start:
{
uint32_t v___x_3623_; uint8_t v___x_3624_; 
v___x_3623_ = 48;
v___x_3624_ = lean_uint32_dec_le(v___x_3623_, v___y_3622_);
if (v___x_3624_ == 0)
{
return v___x_3624_;
}
else
{
uint32_t v___x_3625_; uint8_t v___x_3626_; 
v___x_3625_ = 57;
v___x_3626_ = lean_uint32_dec_le(v___y_3622_, v___x_3625_);
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___y_3627_){
_start:
{
uint32_t v___y_1192__boxed_3628_; uint8_t v_res_3629_; lean_object* v_r_3630_; 
v___y_1192__boxed_3628_ = lean_unbox_uint32(v___y_3627_);
lean_dec(v___y_3627_);
v_res_3629_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___y_1192__boxed_3628_);
v_r_3630_ = lean_box(v_res_3629_);
return v_r_3630_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3631_, uint8_t v___x_3632_, uint32_t v_x_3633_){
_start:
{
uint32_t v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = 187;
v___x_3635_ = lean_uint32_dec_eq(v_x_3633_, v___x_3634_);
if (v___x_3635_ == 0)
{
return v___x_3631_;
}
else
{
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3636_, lean_object* v___x_3637_, lean_object* v_x_3638_){
_start:
{
uint8_t v___x_1203__boxed_3639_; uint8_t v___x_1204__boxed_3640_; uint32_t v_x_1205__boxed_3641_; uint8_t v_res_3642_; lean_object* v_r_3643_; 
v___x_1203__boxed_3639_ = lean_unbox(v___x_3636_);
v___x_1204__boxed_3640_ = lean_unbox(v___x_3637_);
v_x_1205__boxed_3641_ = lean_unbox_uint32(v_x_3638_);
lean_dec(v_x_3638_);
v_res_3642_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_1203__boxed_3639_, v___x_1204__boxed_3640_, v_x_1205__boxed_3641_);
v_r_3643_ = lean_box(v_res_3642_);
return v_r_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3646_, lean_object* v_acc_3647_){
_start:
{
lean_object* v_ss_3649_; lean_object* v_acc_3650_; uint8_t v___x_3659_; 
lean_inc_ref(v_ss_3646_);
v___x_3659_ = lean_substring_isempty(v_ss_3646_);
if (v___x_3659_ == 0)
{
uint32_t v_curr_3660_; uint32_t v___x_3661_; uint8_t v___x_3662_; 
lean_inc_ref(v_ss_3646_);
v_curr_3660_ = lean_substring_front(v_ss_3646_);
v___x_3661_ = 171;
v___x_3662_ = lean_uint32_dec_eq(v_curr_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___f_3663_; lean_object* v___f_3674_; uint8_t v___y_3676_; uint8_t v___y_3688_; uint8_t v___y_3694_; uint32_t v___x_3703_; uint8_t v___x_3704_; 
v___f_3663_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___f_3674_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1));
v___x_3703_ = 65;
v___x_3704_ = lean_uint32_dec_le(v___x_3703_, v_curr_3660_);
if (v___x_3704_ == 0)
{
goto v___jp_3698_;
}
else
{
uint32_t v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = 90;
v___x_3706_ = lean_uint32_dec_le(v_curr_3660_, v___x_3705_);
if (v___x_3706_ == 0)
{
goto v___jp_3698_;
}
else
{
goto v___jp_3664_;
}
}
v___jp_3664_:
{
lean_object* v_idPart_3665_; lean_object* v_startPos_3666_; lean_object* v_stopPos_3667_; lean_object* v_startPos_3668_; lean_object* v_stopPos_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_inc_ref(v_ss_3646_);
v_idPart_3665_ = lean_substring_takewhile(v_ss_3646_, v___f_3663_);
v_startPos_3666_ = lean_ctor_get(v_idPart_3665_, 1);
lean_inc(v_startPos_3666_);
v_stopPos_3667_ = lean_ctor_get(v_idPart_3665_, 2);
lean_inc(v_stopPos_3667_);
v_startPos_3668_ = lean_ctor_get(v_ss_3646_, 1);
v_stopPos_3669_ = lean_ctor_get(v_ss_3646_, 2);
v___x_3670_ = lean_nat_sub(v_stopPos_3667_, v_startPos_3666_);
lean_dec(v_startPos_3666_);
lean_dec(v_stopPos_3667_);
v___x_3671_ = lean_nat_sub(v_stopPos_3669_, v_startPos_3668_);
v___x_3672_ = lean_substring_extract(v_ss_3646_, v___x_3670_, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3673_, 0, v_idPart_3665_);
lean_ctor_set(v___x_3673_, 1, v_acc_3647_);
v_ss_3649_ = v___x_3672_;
v_acc_3650_ = v___x_3673_;
goto v___jp_3648_;
}
v___jp_3675_:
{
if (v___y_3676_ == 0)
{
lean_object* v___x_3677_; 
lean_dec(v_acc_3647_);
lean_dec_ref(v_ss_3646_);
v___x_3677_ = lean_box(0);
return v___x_3677_;
}
else
{
lean_object* v_idPart_3678_; lean_object* v_startPos_3679_; lean_object* v_stopPos_3680_; lean_object* v_startPos_3681_; lean_object* v_stopPos_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_inc_ref(v_ss_3646_);
v_idPart_3678_ = lean_substring_takewhile(v_ss_3646_, v___f_3674_);
v_startPos_3679_ = lean_ctor_get(v_idPart_3678_, 1);
lean_inc(v_startPos_3679_);
v_stopPos_3680_ = lean_ctor_get(v_idPart_3678_, 2);
lean_inc(v_stopPos_3680_);
v_startPos_3681_ = lean_ctor_get(v_ss_3646_, 1);
v_stopPos_3682_ = lean_ctor_get(v_ss_3646_, 2);
v___x_3683_ = lean_nat_sub(v_stopPos_3680_, v_startPos_3679_);
lean_dec(v_startPos_3679_);
lean_dec(v_stopPos_3680_);
v___x_3684_ = lean_nat_sub(v_stopPos_3682_, v_startPos_3681_);
v___x_3685_ = lean_substring_extract(v_ss_3646_, v___x_3683_, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3686_, 0, v_idPart_3678_);
lean_ctor_set(v___x_3686_, 1, v_acc_3647_);
v_ss_3649_ = v___x_3685_;
v_acc_3650_ = v___x_3686_;
goto v___jp_3648_;
}
}
v___jp_3687_:
{
if (v___y_3688_ == 0)
{
uint32_t v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = 48;
v___x_3690_ = lean_uint32_dec_le(v___x_3689_, v_curr_3660_);
if (v___x_3690_ == 0)
{
v___y_3676_ = v___x_3690_;
goto v___jp_3675_;
}
else
{
uint32_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = 57;
v___x_3692_ = lean_uint32_dec_le(v_curr_3660_, v___x_3691_);
v___y_3676_ = v___x_3692_;
goto v___jp_3675_;
}
}
else
{
goto v___jp_3664_;
}
}
v___jp_3693_:
{
if (v___y_3694_ == 0)
{
uint32_t v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = 95;
v___x_3696_ = lean_uint32_dec_eq(v_curr_3660_, v___x_3695_);
if (v___x_3696_ == 0)
{
uint8_t v___x_3697_; 
v___x_3697_ = l_Lean_isLetterLike(v_curr_3660_);
v___y_3688_ = v___x_3697_;
goto v___jp_3687_;
}
else
{
v___y_3688_ = v___x_3696_;
goto v___jp_3687_;
}
}
else
{
goto v___jp_3664_;
}
}
v___jp_3698_:
{
uint32_t v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = 97;
v___x_3700_ = lean_uint32_dec_le(v___x_3699_, v_curr_3660_);
if (v___x_3700_ == 0)
{
v___y_3694_ = v___x_3700_;
goto v___jp_3693_;
}
else
{
uint32_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = 122;
v___x_3702_ = lean_uint32_dec_le(v_curr_3660_, v___x_3701_);
v___y_3694_ = v___x_3702_;
goto v___jp_3693_;
}
}
}
else
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___f_3709_; lean_object* v_escapedPart_3710_; lean_object* v_str_3711_; lean_object* v_startPos_3712_; lean_object* v_stopPos_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3735_; 
v___x_3707_ = lean_box(v___x_3662_);
v___x_3708_ = lean_box(v___x_3659_);
v___f_3709_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3709_, 0, v___x_3707_);
lean_closure_set(v___f_3709_, 1, v___x_3708_);
lean_inc_ref(v_ss_3646_);
v_escapedPart_3710_ = lean_substring_takewhile(v_ss_3646_, v___f_3709_);
v_str_3711_ = lean_ctor_get(v_escapedPart_3710_, 0);
v_startPos_3712_ = lean_ctor_get(v_escapedPart_3710_, 1);
v_stopPos_3713_ = lean_ctor_get(v_escapedPart_3710_, 2);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_escapedPart_3710_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3715_ = v_escapedPart_3710_;
v_isShared_3716_ = v_isSharedCheck_3735_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_stopPos_3713_);
lean_inc(v_startPos_3712_);
lean_inc(v_str_3711_);
lean_dec(v_escapedPart_3710_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3735_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_startPos_3717_; lean_object* v_stopPos_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v_escapedPart_3722_; 
v_startPos_3717_ = lean_ctor_get(v_ss_3646_, 1);
v_stopPos_3718_ = lean_ctor_get(v_ss_3646_, 2);
v___x_3719_ = lean_string_utf8_next(v_str_3711_, v_stopPos_3713_);
lean_dec(v_stopPos_3713_);
lean_inc(v_stopPos_3718_);
v___x_3720_ = lean_string_pos_min(v_stopPos_3718_, v___x_3719_);
lean_inc(v___x_3720_);
lean_inc(v_startPos_3712_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 2, v___x_3720_);
v_escapedPart_3722_ = v___x_3715_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_str_3711_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_startPos_3712_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v___x_3720_);
v_escapedPart_3722_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; uint8_t v___y_3725_; lean_object* v___x_3730_; uint32_t v___x_3731_; uint32_t v___x_3732_; uint8_t v___x_3733_; 
v___x_3723_ = lean_nat_sub(v___x_3720_, v_startPos_3712_);
lean_dec(v_startPos_3712_);
lean_dec(v___x_3720_);
lean_inc(v___x_3723_);
lean_inc_ref(v_escapedPart_3722_);
v___x_3730_ = lean_substring_prev(v_escapedPart_3722_, v___x_3723_);
lean_inc_ref(v_escapedPart_3722_);
v___x_3731_ = lean_substring_get(v_escapedPart_3722_, v___x_3730_);
v___x_3732_ = 187;
v___x_3733_ = lean_uint32_dec_eq(v___x_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
v___y_3725_ = v___x_3662_;
goto v___jp_3724_;
}
else
{
v___y_3725_ = v___x_3659_;
goto v___jp_3724_;
}
v___jp_3724_:
{
if (v___y_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_nat_sub(v_stopPos_3718_, v_startPos_3717_);
v___x_3727_ = lean_substring_extract(v_ss_3646_, v___x_3723_, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_escapedPart_3722_);
lean_ctor_set(v___x_3728_, 1, v_acc_3647_);
v_ss_3649_ = v___x_3727_;
v_acc_3650_ = v___x_3728_;
goto v___jp_3648_;
}
else
{
lean_object* v___x_3729_; 
lean_dec(v___x_3723_);
lean_dec_ref(v_escapedPart_3722_);
lean_dec(v_acc_3647_);
lean_dec_ref(v_ss_3646_);
v___x_3729_ = lean_box(0);
return v___x_3729_;
}
}
}
}
}
}
else
{
lean_object* v___x_3736_; 
lean_dec(v_acc_3647_);
lean_dec_ref(v_ss_3646_);
v___x_3736_ = lean_box(0);
return v___x_3736_;
}
v___jp_3648_:
{
uint32_t v___x_3651_; uint32_t v___x_3652_; uint8_t v___x_3653_; 
lean_inc_ref(v_ss_3649_);
v___x_3651_ = lean_substring_front(v_ss_3649_);
v___x_3652_ = 46;
v___x_3653_ = lean_uint32_dec_eq(v___x_3651_, v___x_3652_);
if (v___x_3653_ == 0)
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_substring_isempty(v_ss_3649_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
lean_dec(v_acc_3650_);
v___x_3655_ = lean_box(0);
return v___x_3655_;
}
else
{
return v_acc_3650_;
}
}
else
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_unsigned_to_nat(1u);
v___x_3657_ = lean_substring_drop(v_ss_3649_, v___x_3656_);
v_ss_3646_ = v___x_3657_;
v_acc_3647_ = v_acc_3650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = lean_box(0);
v___x_3739_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3737_, v___x_3738_);
v___x_3740_ = l_List_reverse___redArg(v___x_3739_);
return v___x_3740_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3744_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3745_ = lean_unsigned_to_nat(10u);
v___x_3746_ = lean_unsigned_to_nat(1230u);
v___x_3747_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3748_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3749_ = l_mkPanicMessageWithDecl(v___x_3748_, v___x_3747_, v___x_3746_, v___x_3745_, v___x_3744_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3750_, lean_object* v_x_3751_){
_start:
{
if (lean_obj_tag(v_x_3751_) == 0)
{
lean_inc(v_init_3750_);
return v_init_3750_;
}
else
{
lean_object* v_head_3752_; lean_object* v_tail_3753_; lean_object* v___x_3754_; lean_object* v_comp_3755_; uint8_t v___y_3757_; uint32_t v___x_3764_; uint32_t v___x_3765_; uint8_t v___x_3766_; 
v_head_3752_ = lean_ctor_get(v_x_3751_, 0);
lean_inc(v_head_3752_);
v_tail_3753_ = lean_ctor_get(v_x_3751_, 1);
lean_inc(v_tail_3753_);
lean_dec_ref(v_x_3751_);
v___x_3754_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3750_, v_tail_3753_);
v_comp_3755_ = lean_substring_tostring(v_head_3752_);
lean_inc_ref(v_comp_3755_);
v___x_3764_ = lean_string_front(v_comp_3755_);
v___x_3765_ = 171;
v___x_3766_ = lean_uint32_dec_eq(v___x_3764_, v___x_3765_);
if (v___x_3766_ == 0)
{
uint32_t v___x_3767_; uint8_t v___x_3768_; 
v___x_3767_ = 48;
v___x_3768_ = lean_uint32_dec_le(v___x_3767_, v___x_3764_);
if (v___x_3768_ == 0)
{
v___y_3757_ = v___x_3768_;
goto v___jp_3756_;
}
else
{
uint32_t v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = 57;
v___x_3770_ = lean_uint32_dec_le(v___x_3764_, v___x_3769_);
v___y_3757_ = v___x_3770_;
goto v___jp_3756_;
}
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_string_drop(v_comp_3755_, v___x_3771_);
v___x_3773_ = lean_string_dropright(v___x_3772_, v___x_3771_);
v___x_3774_ = l_Lean_Name_str___override(v___x_3754_, v___x_3773_);
return v___x_3774_;
}
v___jp_3756_:
{
if (v___y_3757_ == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Name_str___override(v___x_3754_, v_comp_3755_);
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3755_);
lean_dec_ref(v_comp_3755_);
if (lean_obj_tag(v___x_3759_) == 1)
{
lean_object* v_val_3760_; lean_object* v___x_3761_; 
v_val_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_val_3760_);
lean_dec_ref(v___x_3759_);
v___x_3761_ = l_Lean_Name_num___override(v___x_3754_, v_val_3760_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec(v___x_3759_);
lean_dec(v___x_3754_);
v___x_3762_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3763_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3762_);
return v___x_3763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3775_, lean_object* v_x_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3775_, v_x_3776_);
lean_dec(v_init_3775_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3778_){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = lean_box(0);
v___x_3780_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3778_, v___x_3779_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_box(0);
return v___x_3781_;
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = lean_box(0);
v___x_3783_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3782_, v___x_3780_);
return v___x_3783_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3784_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = lean_string_utf8_byte_size(v_s_3784_);
v___x_3787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3787_, 0, v_s_3784_);
lean_ctor_set(v___x_3787_, 1, v___x_3785_);
lean_ctor_set(v___x_3787_, 2, v___x_3786_);
v___x_3788_ = l_Substring_Raw_toName(v___x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3789_){
_start:
{
lean_object* v___x_3790_; uint32_t v___x_3791_; uint32_t v___x_3792_; uint8_t v___x_3793_; 
v___x_3790_ = lean_unsigned_to_nat(0u);
v___x_3791_ = lean_string_utf8_get(v_s_3789_, v___x_3790_);
v___x_3792_ = 96;
v___x_3793_ = lean_uint32_dec_eq(v___x_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
lean_dec_ref(v_s_3789_);
v___x_3794_ = lean_box(0);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3795_ = lean_string_utf8_byte_size(v_s_3789_);
v___x_3796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3796_, 0, v_s_3789_);
lean_ctor_set(v___x_3796_, 1, v___x_3790_);
lean_ctor_set(v___x_3796_, 2, v___x_3795_);
v___x_3797_ = lean_unsigned_to_nat(1u);
v___x_3798_ = lean_substring_drop(v___x_3796_, v___x_3797_);
v___x_3799_ = l_Substring_Raw_toName(v___x_3798_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_box(0);
return v___x_3800_;
}
else
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3802_){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3804_ = l_Lean_Syntax_isLit_x3f(v___x_3803_, v_stx_3802_);
if (lean_obj_tag(v___x_3804_) == 1)
{
lean_object* v_val_3805_; lean_object* v___x_3806_; 
v_val_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_val_3805_);
lean_dec_ref(v___x_3804_);
v___x_3806_ = l_Lean_Syntax_decodeNameLit(v_val_3805_);
return v___x_3806_;
}
else
{
lean_object* v___x_3807_; 
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
return v___x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3808_);
lean_dec(v_stx_3808_);
return v_res_3809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3810_){
_start:
{
if (lean_obj_tag(v_x_3810_) == 1)
{
lean_object* v_args_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_args_3811_ = lean_ctor_get(v_x_3810_, 2);
v___x_3812_ = lean_unsigned_to_nat(0u);
v___x_3813_ = lean_array_get_size(v_args_3811_);
v___x_3814_ = lean_nat_dec_lt(v___x_3812_, v___x_3813_);
return v___x_3814_;
}
else
{
uint8_t v___x_3815_; 
v___x_3815_ = 0;
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3816_){
_start:
{
uint8_t v_res_3817_; lean_object* v_r_3818_; 
v_res_3817_ = l_Lean_Syntax_hasArgs(v_x_3816_);
lean_dec(v_x_3816_);
v_r_3818_ = lean_box(v_res_3817_);
return v_r_3818_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3819_) == 2)
{
uint8_t v___x_3820_; 
v___x_3820_ = 1;
return v___x_3820_;
}
else
{
uint8_t v___x_3821_; 
v___x_3821_ = 0;
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3822_){
_start:
{
uint8_t v_res_3823_; lean_object* v_r_3824_; 
v_res_3823_ = l_Lean_Syntax_isAtom(v_x_3822_);
lean_dec(v_x_3822_);
v_r_3824_ = lean_box(v_res_3823_);
return v_r_3824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3825_, lean_object* v_x_3826_){
_start:
{
if (lean_obj_tag(v_x_3826_) == 2)
{
lean_object* v_val_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_val_3827_ = lean_ctor_get(v_x_3826_, 1);
lean_inc_ref(v_val_3827_);
lean_dec_ref(v_x_3826_);
v___x_3828_ = lean_string_trim(v_val_3827_);
v___x_3829_ = lean_string_trim(v_token_3825_);
v___x_3830_ = lean_string_dec_eq(v___x_3828_, v___x_3829_);
lean_dec_ref(v___x_3829_);
lean_dec_ref(v___x_3828_);
return v___x_3830_;
}
else
{
uint8_t v___x_3831_; 
lean_dec(v_x_3826_);
lean_dec_ref(v_token_3825_);
v___x_3831_ = 0;
return v___x_3831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3832_, lean_object* v_x_3833_){
_start:
{
uint8_t v_res_3834_; lean_object* v_r_3835_; 
v_res_3834_ = l_Lean_Syntax_isToken(v_token_3832_, v_x_3833_);
v_r_3835_ = lean_box(v_res_3834_);
return v_r_3835_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3836_){
_start:
{
switch(lean_obj_tag(v_stx_3836_))
{
case 1:
{
lean_object* v_kind_3837_; lean_object* v_args_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_kind_3837_ = lean_ctor_get(v_stx_3836_, 1);
v_args_3838_ = lean_ctor_get(v_stx_3836_, 2);
v___x_3839_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3840_ = lean_name_eq(v_kind_3837_, v___x_3839_);
if (v___x_3840_ == 0)
{
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v___x_3841_ = lean_array_get_size(v_args_3838_);
v___x_3842_ = lean_unsigned_to_nat(0u);
v___x_3843_ = lean_nat_dec_eq(v___x_3841_, v___x_3842_);
return v___x_3843_;
}
}
case 0:
{
uint8_t v___x_3844_; 
v___x_3844_ = 1;
return v___x_3844_;
}
default: 
{
uint8_t v___x_3845_; 
v___x_3845_ = 0;
return v___x_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3846_){
_start:
{
uint8_t v_res_3847_; lean_object* v_r_3848_; 
v_res_3847_ = l_Lean_Syntax_isNone(v_stx_3846_);
lean_dec(v_stx_3846_);
v_r_3848_ = lean_box(v_res_3847_);
return v_r_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3849_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_Syntax_getOptional_x3f(v_stx_3849_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v___x_3851_; 
v___x_3851_ = lean_box(0);
return v___x_3851_;
}
else
{
lean_object* v_val_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3860_; 
v_val_3852_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3854_ = v___x_3850_;
v_isShared_3855_ = v_isSharedCheck_3860_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_val_3852_);
lean_dec(v___x_3850_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3860_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = l_Lean_Syntax_getId(v_val_3852_);
lean_dec(v_val_3852_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3856_);
v___x_3858_ = v___x_3854_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3861_);
lean_dec(v_stx_3861_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3863_, lean_object* v_x_3864_){
_start:
{
if (lean_obj_tag(v_x_3864_) == 1)
{
lean_object* v_args_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v_args_3865_ = lean_ctor_get(v_x_3864_, 2);
lean_inc_ref(v_p_3863_);
lean_inc_ref(v_x_3864_);
v___x_3866_ = lean_apply_1(v_p_3863_, v_x_3864_);
v___x_3867_ = lean_unbox(v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; size_t v_sz_3870_; size_t v___x_3871_; lean_object* v___x_3872_; lean_object* v_fst_3873_; 
lean_inc_ref(v_args_3865_);
lean_dec_ref(v_x_3864_);
v___x_3868_ = lean_box(0);
v___x_3869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3870_ = lean_array_size(v_args_3865_);
v___x_3871_ = ((size_t)0ULL);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3863_, v_args_3865_, v_sz_3870_, v___x_3871_, v___x_3869_);
lean_dec_ref(v_args_3865_);
v_fst_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_fst_3873_);
lean_dec_ref(v___x_3872_);
if (lean_obj_tag(v_fst_3873_) == 0)
{
return v___x_3868_;
}
else
{
lean_object* v_val_3874_; 
v_val_3874_ = lean_ctor_get(v_fst_3873_, 0);
lean_inc(v_val_3874_);
lean_dec_ref(v_fst_3873_);
return v_val_3874_;
}
}
else
{
lean_object* v___x_3875_; 
lean_dec_ref(v_p_3863_);
v___x_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3875_, 0, v_x_3864_);
return v___x_3875_;
}
}
else
{
lean_object* v___x_3876_; uint8_t v___x_3877_; 
lean_inc(v_x_3864_);
v___x_3876_ = lean_apply_1(v_p_3863_, v_x_3864_);
v___x_3877_ = lean_unbox(v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec(v_x_3864_);
v___x_3878_ = lean_box(0);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v_x_3864_);
return v___x_3879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3880_, lean_object* v_as_3881_, size_t v_sz_3882_, size_t v_i_3883_, lean_object* v_b_3884_){
_start:
{
uint8_t v___x_3885_; 
v___x_3885_ = lean_usize_dec_lt(v_i_3883_, v_sz_3882_);
if (v___x_3885_ == 0)
{
lean_dec_ref(v_p_3880_);
return v_b_3884_;
}
else
{
lean_object* v___x_3886_; lean_object* v_a_3887_; lean_object* v___x_3888_; 
lean_dec_ref(v_b_3884_);
v___x_3886_ = lean_box(0);
v_a_3887_ = lean_array_uget_borrowed(v_as_3881_, v_i_3883_);
lean_inc(v_a_3887_);
lean_inc_ref(v_p_3880_);
v___x_3888_ = l_Lean_Syntax_findAux(v_p_3880_, v_a_3887_);
if (lean_obj_tag(v___x_3888_) == 1)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_dec_ref(v_p_3880_);
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
lean_ctor_set(v___x_3890_, 1, v___x_3886_);
return v___x_3890_;
}
else
{
lean_object* v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; 
lean_dec(v___x_3888_);
v___x_3891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3892_ = ((size_t)1ULL);
v___x_3893_ = lean_usize_add(v_i_3883_, v___x_3892_);
v_i_3883_ = v___x_3893_;
v_b_3884_ = v___x_3891_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3895_, lean_object* v_as_3896_, lean_object* v_sz_3897_, lean_object* v_i_3898_, lean_object* v_b_3899_){
_start:
{
size_t v_sz_boxed_3900_; size_t v_i_boxed_3901_; lean_object* v_res_3902_; 
v_sz_boxed_3900_ = lean_unbox_usize(v_sz_3897_);
lean_dec(v_sz_3897_);
v_i_boxed_3901_ = lean_unbox_usize(v_i_3898_);
lean_dec(v_i_3898_);
v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3895_, v_as_3896_, v_sz_boxed_3900_, v_i_boxed_3901_, v_b_3899_);
lean_dec_ref(v_as_3896_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3903_, lean_object* v_p_3904_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Syntax_findAux(v_p_3904_, v_stx_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_Syntax_isNatLit_x3f(v_s_3906_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v___x_3908_; 
v___x_3908_ = lean_unsigned_to_nat(0u);
return v___x_3908_;
}
else
{
lean_object* v_val_3909_; 
v_val_3909_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_val_3909_);
lean_dec_ref(v___x_3907_);
return v_val_3909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_TSyntax_getNat(v_s_3910_);
lean_dec(v_s_3910_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3915_){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3917_ = l_Lean_Syntax_isLit_x3f(v___x_3916_, v_stx_3915_);
if (lean_obj_tag(v___x_3917_) == 1)
{
lean_object* v_val_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_val_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_val_3918_);
lean_dec_ref(v___x_3917_);
v___x_3919_ = lean_unsigned_to_nat(0u);
v___x_3920_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3918_, v___x_3919_, v___x_3919_);
lean_dec(v_val_3918_);
return v___x_3920_;
}
else
{
lean_object* v___x_3921_; 
lean_dec(v___x_3917_);
v___x_3921_ = lean_box(0);
return v___x_3921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3922_);
lean_dec(v_stx_3922_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3924_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v___x_3926_; 
v___x_3926_ = lean_unsigned_to_nat(0u);
return v___x_3926_;
}
else
{
lean_object* v_val_3927_; 
v_val_3927_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_val_3927_);
lean_dec_ref(v___x_3925_);
return v_val_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_TSyntax_getHexNumVal(v_s_3928_);
lean_dec(v_s_3928_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3930_, lean_object* v_p_3931_, lean_object* v_n_3932_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_string_utf8_at_end(v_s_3930_, v_p_3931_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; uint32_t v___x_3935_; uint32_t v___x_3936_; uint8_t v___x_3937_; 
v___x_3934_ = lean_string_utf8_next(v_s_3930_, v_p_3931_);
v___x_3935_ = lean_string_utf8_get(v_s_3930_, v_p_3931_);
lean_dec(v_p_3931_);
v___x_3936_ = 95;
v___x_3937_ = lean_uint32_dec_eq(v___x_3935_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = lean_nat_add(v_n_3932_, v___x_3938_);
lean_dec(v_n_3932_);
v_p_3931_ = v___x_3934_;
v_n_3932_ = v___x_3939_;
goto _start;
}
else
{
v_p_3931_ = v___x_3934_;
goto _start;
}
}
else
{
lean_dec(v_p_3931_);
return v_n_3932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3942_, lean_object* v_p_3943_, lean_object* v_n_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3942_, v_p_3943_, v_n_3944_);
lean_dec_ref(v_s_3942_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3946_){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3948_ = l_Lean_Syntax_isLit_x3f(v___x_3947_, v_s_3946_);
if (lean_obj_tag(v___x_3948_) == 1)
{
lean_object* v_val_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_val_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_val_3949_);
lean_dec_ref(v___x_3948_);
v___x_3950_ = lean_unsigned_to_nat(0u);
v___x_3951_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3949_, v___x_3950_, v___x_3950_);
lean_dec(v_val_3949_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; 
lean_dec(v___x_3948_);
v___x_3952_ = lean_unsigned_to_nat(0u);
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_TSyntax_getHexNumSize(v_s_3953_);
lean_dec(v_s_3953_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3955_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Syntax_getId(v_s_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_TSyntax_getId(v_s_3957_);
lean_dec(v_s_3957_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3966_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3966_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; 
v___x_3968_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3968_;
}
else
{
lean_object* v_val_3969_; 
v_val_3969_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_val_3969_);
lean_dec_ref(v___x_3967_);
return v_val_3969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_TSyntax_getScientific(v_s_3970_);
lean_dec(v_s_3970_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_Syntax_isStrLit_x3f(v_s_3972_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3974_; 
v___x_3974_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3974_;
}
else
{
lean_object* v_val_3975_; 
v_val_3975_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_val_3975_);
lean_dec_ref(v___x_3973_);
return v_val_3975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_TSyntax_getString(v_s_3976_);
lean_dec(v_s_3976_);
return v_res_3977_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_Syntax_isCharLit_x3f(v_s_3978_);
if (lean_obj_tag(v___x_3979_) == 0)
{
uint32_t v___x_3980_; 
v___x_3980_ = 65;
return v___x_3980_;
}
else
{
lean_object* v_val_3981_; uint32_t v___x_3982_; 
v_val_3981_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3981_);
lean_dec_ref(v___x_3979_);
v___x_3982_ = lean_unbox_uint32(v_val_3981_);
lean_dec(v_val_3981_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3983_){
_start:
{
uint32_t v_res_3984_; lean_object* v_r_3985_; 
v_res_3984_ = l_Lean_TSyntax_getChar(v_s_3983_);
lean_dec(v_s_3983_);
v_r_3985_ = lean_box_uint32(v_res_3984_);
return v_r_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Syntax_isNameLit_x3f(v_s_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_box(0);
return v___x_3988_;
}
else
{
lean_object* v_val_3989_; 
v_val_3989_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_val_3989_);
lean_dec_ref(v___x_3987_);
return v_val_3989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_TSyntax_getName(v_s_3990_);
lean_dec(v_s_3990_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3992_){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unsigned_to_nat(0u);
v___x_3994_ = l_Lean_Syntax_getArg(v_s_3992_, v___x_3993_);
v___x_3995_ = l_Lean_Syntax_getId(v___x_3994_);
lean_dec(v___x_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_TSyntax_getHygieneInfo(v_s_3996_);
lean_dec(v_s_3996_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3998_, v_a_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_4001_, v_a_4002_);
lean_dec_ref(v_a_4002_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_4004_){
_start:
{
lean_object* v___f_4005_; 
v___f_4005_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4005_, 0, v_sep_4004_);
return v___f_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_4006_, lean_object* v_sep_4007_){
_start:
{
lean_object* v___f_4008_; 
v___f_4008_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4008_, 0, v_sep_4007_);
return v___f_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_4009_, lean_object* v_sep_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_4009_, v_sep_4010_);
lean_dec(v_k_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_4012_, lean_object* v_val_4013_, uint8_t v_canonical_4014_){
_start:
{
lean_object* v___x_4015_; lean_object* v_src_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v_imported_4019_; lean_object* v_ctx_4020_; lean_object* v_scopes_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4037_; 
v___x_4015_ = lean_unsigned_to_nat(0u);
v_src_4016_ = l_Lean_Syntax_getArg(v_s_4012_, v___x_4015_);
v___x_4017_ = l_Lean_Syntax_getId(v_src_4016_);
v___x_4018_ = l_Lean_extractMacroScopes(v___x_4017_);
v_imported_4019_ = lean_ctor_get(v___x_4018_, 1);
v_ctx_4020_ = lean_ctor_get(v___x_4018_, 2);
v_scopes_4021_ = lean_ctor_get(v___x_4018_, 3);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v___x_4018_, 0);
lean_dec(v_unused_4038_);
v___x_4023_ = v___x_4018_;
v_isShared_4024_ = v_isSharedCheck_4037_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_scopes_4021_);
lean_inc(v_ctx_4020_);
lean_inc(v_imported_4019_);
lean_dec(v___x_4018_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4037_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_inc(v_val_4013_);
v___x_4025_ = lean_erase_macro_scopes(v_val_4013_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v___x_4025_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_imported_4019_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_ctx_4020_);
lean_ctor_set(v_reuseFailAlloc_4036_, 3, v_scopes_4021_);
v___x_4027_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v_id_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v_id_4028_ = l_Lean_MacroScopesView_review(v___x_4027_);
v___x_4029_ = l_Lean_SourceInfo_fromRef(v_src_4016_, v_canonical_4014_);
lean_dec(v_src_4016_);
v___x_4030_ = 1;
v___x_4031_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_4013_, v___x_4030_);
v___x_4032_ = lean_string_utf8_byte_size(v___x_4031_);
v___x_4033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4015_);
lean_ctor_set(v___x_4033_, 2, v___x_4032_);
v___x_4034_ = lean_box(0);
v___x_4035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4029_);
lean_ctor_set(v___x_4035_, 1, v___x_4033_);
lean_ctor_set(v___x_4035_, 2, v_id_4028_);
lean_ctor_set(v___x_4035_, 3, v___x_4034_);
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4039_, lean_object* v_val_4040_, lean_object* v_canonical_4041_){
_start:
{
uint8_t v_canonical_boxed_4042_; lean_object* v_res_4043_; 
v_canonical_boxed_4042_ = lean_unbox(v_canonical_4041_);
v_res_4043_ = l_Lean_HygieneInfo_mkIdent(v_s_4039_, v_val_4040_, v_canonical_boxed_4042_);
lean_dec(v_s_4039_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4044_, lean_object* v_inst_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_apply_1(v_inst_4044_, v_a_4046_);
v___x_4048_ = lean_apply_1(v_inst_4045_, v___x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4049_, lean_object* v_inst_4050_){
_start:
{
lean_object* v___f_4051_; 
v___f_4051_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4051_, 0, v_inst_4049_);
lean_closure_set(v___f_4051_, 1, v_inst_4050_);
return v___f_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4052_, lean_object* v_k_4053_, lean_object* v_k_x27_4054_, lean_object* v_inst_4055_, lean_object* v_inst_4056_){
_start:
{
lean_object* v___f_4057_; 
v___f_4057_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4057_, 0, v_inst_4055_);
lean_closure_set(v___f_4057_, 1, v_inst_4056_);
return v___f_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4058_, lean_object* v_k_4059_, lean_object* v_k_x27_4060_, lean_object* v_inst_4061_, lean_object* v_inst_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4058_, v_k_4059_, v_k_x27_4060_, v_inst_4061_, v_inst_4062_);
lean_dec(v_k_x27_4060_);
lean_dec(v_k_4059_);
return v_res_4063_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4072_ = l_Lean_mkCIdent(v___x_4071_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4078_ = l_Lean_mkCIdent(v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4079_){
_start:
{
if (v_x_4079_ == 0)
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4080_;
}
else
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4082_){
_start:
{
uint8_t v_x_85__boxed_4083_; lean_object* v_res_4084_; 
v_x_85__boxed_4083_ = lean_unbox(v_x_4082_);
v_res_4084_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4083_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_box(2);
v___x_4089_ = l_Lean_Syntax_mkCharLit(v_val_4087_, v___x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4090_){
_start:
{
uint32_t v_val_boxed_4091_; lean_object* v_res_4092_; 
v_val_boxed_4091_ = lean_unbox_uint32(v_val_4090_);
lean_dec(v_val_4090_);
v_res_4092_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4091_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_box(2);
v___x_4097_ = l_Lean_Syntax_mkStrLit(v_val_4095_, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4100_){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = l_Nat_reprFast(v_n_4100_);
v___x_4102_ = lean_box(2);
v___x_4103_ = l_Lean_Syntax_mkNumLit(v___x_4101_, v___x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4111_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4112_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4113_ = lean_substring_tostring(v_s_4111_);
v___x_4114_ = lean_box(2);
v___x_4115_ = l_Lean_Syntax_mkStrLit(v___x_4113_, v___x_4114_);
v___x_4116_ = lean_unsigned_to_nat(1u);
v___x_4117_ = lean_mk_empty_array_with_capacity(v___x_4116_);
v___x_4118_ = lean_array_push(v___x_4117_, v___x_4115_);
v___x_4119_ = l_Lean_Syntax_mkCApp(v___x_4112_, v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4122_, lean_object* v_x_4123_){
_start:
{
switch(lean_obj_tag(v_x_4123_))
{
case 0:
{
uint8_t v___x_4124_; 
v___x_4124_ = l_List_isEmpty___redArg(v_acc_4122_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_acc_4122_);
return v___x_4125_;
}
else
{
lean_object* v___x_4126_; 
lean_dec(v_acc_4122_);
v___x_4126_ = lean_box(0);
return v___x_4126_;
}
}
case 1:
{
lean_object* v_pre_4127_; lean_object* v_str_4128_; lean_object* v_val_4130_; lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v_pre_4127_ = lean_ctor_get(v_x_4123_, 0);
lean_inc(v_pre_4127_);
v_str_4128_ = lean_ctor_get(v_x_4123_, 1);
lean_inc_ref(v_str_4128_);
lean_dec_ref(v_x_4123_);
v___x_4133_ = lean_unsigned_to_nat(0u);
v___x_4134_ = lean_string_utf8_byte_size(v_str_4128_);
v___x_4135_ = lean_nat_dec_lt(v___x_4133_, v___x_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4136_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4137_ = lean_string_append(v___x_4136_, v_str_4128_);
lean_dec_ref(v_str_4128_);
v___x_4138_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4139_ = lean_string_append(v___x_4137_, v___x_4138_);
v_val_4130_ = v___x_4139_;
goto v___jp_4129_;
}
else
{
lean_object* v___f_4140_; lean_object* v___f_4141_; uint8_t v___y_4155_; uint32_t v___y_4157_; uint8_t v___y_4158_; uint32_t v___y_4163_; uint8_t v___y_4169_; uint8_t v_c_4178_; uint8_t v___y_4180_; uint8_t v___y_4184_; uint8_t v___x_4189_; uint8_t v___x_4190_; 
v___f_4140_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v___f_4141_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v_c_4178_ = lean_string_get_byte_fast(v_str_4128_, v___x_4133_);
v___x_4189_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4190_ = lean_uint8_dec_le(v___x_4189_, v_c_4178_);
if (v___x_4190_ == 0)
{
v___y_4184_ = v___x_4190_;
goto v___jp_4183_;
}
else
{
uint8_t v___x_4191_; uint8_t v___x_4192_; 
v___x_4191_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4192_ = lean_uint8_dec_le(v_c_4178_, v___x_4191_);
v___y_4184_ = v___x_4192_;
goto v___jp_4183_;
}
v___jp_4142_:
{
uint8_t v___x_4143_; 
lean_inc_ref(v_str_4128_);
v___x_4143_ = lean_string_any(v_str_4128_, v___f_4141_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4144_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4145_ = lean_string_append(v___x_4144_, v_str_4128_);
lean_dec_ref(v_str_4128_);
v___x_4146_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4147_ = lean_string_append(v___x_4145_, v___x_4146_);
v_val_4130_ = v___x_4147_;
goto v___jp_4129_;
}
else
{
lean_object* v___x_4148_; 
lean_dec_ref(v_str_4128_);
lean_dec(v_pre_4127_);
lean_dec(v_acc_4122_);
v___x_4148_ = lean_box(0);
return v___x_4148_;
}
}
v___jp_4149_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
lean_inc_ref(v_str_4128_);
v___x_4150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4150_, 0, v_str_4128_);
lean_ctor_set(v___x_4150_, 1, v___x_4133_);
lean_ctor_set(v___x_4150_, 2, v___x_4134_);
v___x_4151_ = lean_unsigned_to_nat(1u);
v___x_4152_ = lean_substring_drop(v___x_4150_, v___x_4151_);
v___x_4153_ = lean_substring_all(v___x_4152_, v___f_4140_);
if (v___x_4153_ == 0)
{
goto v___jp_4142_;
}
else
{
v_val_4130_ = v_str_4128_;
goto v___jp_4129_;
}
}
v___jp_4154_:
{
if (v___y_4155_ == 0)
{
goto v___jp_4142_;
}
else
{
goto v___jp_4149_;
}
}
v___jp_4156_:
{
if (v___y_4158_ == 0)
{
uint32_t v___x_4159_; uint8_t v___x_4160_; 
v___x_4159_ = 95;
v___x_4160_ = lean_uint32_dec_eq(v___y_4157_, v___x_4159_);
if (v___x_4160_ == 0)
{
uint8_t v___x_4161_; 
v___x_4161_ = l_Lean_isLetterLike(v___y_4157_);
v___y_4155_ = v___x_4161_;
goto v___jp_4154_;
}
else
{
v___y_4155_ = v___x_4160_;
goto v___jp_4154_;
}
}
else
{
goto v___jp_4149_;
}
}
v___jp_4162_:
{
uint32_t v___x_4164_; uint8_t v___x_4165_; 
v___x_4164_ = 97;
v___x_4165_ = lean_uint32_dec_le(v___x_4164_, v___y_4163_);
if (v___x_4165_ == 0)
{
v___y_4157_ = v___y_4163_;
v___y_4158_ = v___x_4165_;
goto v___jp_4156_;
}
else
{
uint32_t v___x_4166_; uint8_t v___x_4167_; 
v___x_4166_ = 122;
v___x_4167_ = lean_uint32_dec_le(v___y_4163_, v___x_4166_);
v___y_4157_ = v___y_4163_;
v___y_4158_ = v___x_4167_;
goto v___jp_4156_;
}
}
v___jp_4168_:
{
if (v___y_4169_ == 0)
{
uint32_t v___x_4170_; uint32_t v___x_4171_; uint8_t v___x_4172_; 
v___x_4170_ = lean_string_utf8_get(v_str_4128_, v___x_4133_);
v___x_4171_ = 65;
v___x_4172_ = lean_uint32_dec_le(v___x_4171_, v___x_4170_);
if (v___x_4172_ == 0)
{
v___y_4163_ = v___x_4170_;
goto v___jp_4162_;
}
else
{
uint32_t v___x_4173_; uint8_t v___x_4174_; 
v___x_4173_ = 90;
v___x_4174_ = lean_uint32_dec_le(v___x_4170_, v___x_4173_);
if (v___x_4174_ == 0)
{
v___y_4163_ = v___x_4170_;
goto v___jp_4162_;
}
else
{
goto v___jp_4149_;
}
}
}
else
{
v_val_4130_ = v_str_4128_;
goto v___jp_4129_;
}
}
v___jp_4175_:
{
lean_object* v___x_4176_; uint8_t v___x_4177_; 
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4128_, v___x_4176_);
v___y_4169_ = v___x_4177_;
goto v___jp_4168_;
}
v___jp_4179_:
{
if (v___y_4180_ == 0)
{
uint8_t v___x_4181_; uint8_t v___x_4182_; 
v___x_4181_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4182_ = lean_uint8_dec_eq(v_c_4178_, v___x_4181_);
if (v___x_4182_ == 0)
{
v___y_4169_ = v___x_4182_;
goto v___jp_4168_;
}
else
{
goto v___jp_4175_;
}
}
else
{
goto v___jp_4175_;
}
}
v___jp_4183_:
{
if (v___y_4184_ == 0)
{
uint8_t v___x_4185_; uint8_t v___x_4186_; 
v___x_4185_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4186_ = lean_uint8_dec_le(v___x_4185_, v_c_4178_);
if (v___x_4186_ == 0)
{
v___y_4180_ = v___x_4186_;
goto v___jp_4179_;
}
else
{
uint8_t v___x_4187_; uint8_t v___x_4188_; 
v___x_4187_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4188_ = lean_uint8_dec_le(v_c_4178_, v___x_4187_);
v___y_4180_ = v___x_4188_;
goto v___jp_4179_;
}
}
else
{
goto v___jp_4175_;
}
}
}
v___jp_4129_:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4131_, 0, v_val_4130_);
lean_ctor_set(v___x_4131_, 1, v_acc_4122_);
v_acc_4122_ = v___x_4131_;
v_x_4123_ = v_pre_4127_;
goto _start;
}
}
default: 
{
lean_object* v___x_4193_; 
lean_dec_ref(v_x_4123_);
lean_dec(v_acc_4122_);
v___x_4193_ = lean_box(0);
return v___x_4193_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4201_ = l_Lean_mkCIdent(v___x_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4212_){
_start:
{
switch(lean_obj_tag(v_x_4212_))
{
case 0:
{
lean_object* v___x_4213_; 
v___x_4213_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4213_;
}
case 1:
{
lean_object* v_pre_4214_; lean_object* v_str_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v_pre_4214_ = lean_ctor_get(v_x_4212_, 0);
lean_inc(v_pre_4214_);
v_str_4215_ = lean_ctor_get(v_x_4212_, 1);
lean_inc_ref(v_str_4215_);
lean_dec_ref(v_x_4212_);
v___x_4216_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4217_ = l_Lean_quoteNameMk(v_pre_4214_);
v___x_4218_ = lean_box(2);
v___x_4219_ = l_Lean_Syntax_mkStrLit(v_str_4215_, v___x_4218_);
v___x_4220_ = lean_unsigned_to_nat(2u);
v___x_4221_ = lean_mk_empty_array_with_capacity(v___x_4220_);
v___x_4222_ = lean_array_push(v___x_4221_, v___x_4217_);
v___x_4223_ = lean_array_push(v___x_4222_, v___x_4219_);
v___x_4224_ = l_Lean_Syntax_mkCApp(v___x_4216_, v___x_4223_);
return v___x_4224_;
}
default: 
{
lean_object* v_pre_4225_; lean_object* v_i_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_pre_4225_ = lean_ctor_get(v_x_4212_, 0);
lean_inc(v_pre_4225_);
v_i_4226_ = lean_ctor_get(v_x_4212_, 1);
lean_inc(v_i_4226_);
lean_dec_ref(v_x_4212_);
v___x_4227_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4228_ = l_Lean_quoteNameMk(v_pre_4225_);
v___x_4229_ = l_Nat_reprFast(v_i_4226_);
v___x_4230_ = lean_box(2);
v___x_4231_ = l_Lean_Syntax_mkNumLit(v___x_4229_, v___x_4230_);
v___x_4232_ = lean_unsigned_to_nat(2u);
v___x_4233_ = lean_mk_empty_array_with_capacity(v___x_4232_);
v___x_4234_ = lean_array_push(v___x_4233_, v___x_4228_);
v___x_4235_ = lean_array_push(v___x_4234_, v___x_4231_);
v___x_4236_ = l_Lean_Syntax_mkCApp(v___x_4227_, v___x_4235_);
return v___x_4236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4243_){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4244_ = lean_box(0);
lean_inc(v_n_4243_);
v___x_4245_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4244_, v_n_4243_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_quoteNameMk(v_n_4243_);
return v___x_4246_;
}
else
{
lean_object* v_val_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec(v_n_4243_);
v_val_4247_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_val_4247_);
lean_dec_ref(v___x_4245_);
v___x_4248_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4249_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4250_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4251_ = lean_string_intercalate(v___x_4250_, v_val_4247_);
v___x_4252_ = lean_string_append(v___x_4249_, v___x_4251_);
lean_dec_ref(v___x_4251_);
v___x_4253_ = lean_box(2);
v___x_4254_ = l_Lean_Syntax_mkNameLit(v___x_4252_, v___x_4253_);
v___x_4255_ = lean_unsigned_to_nat(1u);
v___x_4256_ = lean_mk_empty_array_with_capacity(v___x_4255_);
v___x_4257_ = lean_array_push(v___x_4256_, v___x_4254_);
v___x_4258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4253_);
lean_ctor_set(v___x_4258_, 1, v___x_4248_);
lean_ctor_set(v___x_4258_, 2, v___x_4257_);
return v___x_4258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4259_){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = lean_box(0);
lean_inc(v_n_4259_);
v___x_4261_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4260_, v_n_4259_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_quoteNameMk(v_n_4259_);
return v___x_4262_;
}
else
{
lean_object* v_val_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec(v_n_4259_);
v_val_4263_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_val_4263_);
lean_dec_ref(v___x_4261_);
v___x_4264_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4265_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4266_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4267_ = lean_string_intercalate(v___x_4266_, v_val_4263_);
v___x_4268_ = lean_string_append(v___x_4265_, v___x_4267_);
lean_dec_ref(v___x_4267_);
v___x_4269_ = lean_box(2);
v___x_4270_ = l_Lean_Syntax_mkNameLit(v___x_4268_, v___x_4269_);
v___x_4271_ = lean_unsigned_to_nat(1u);
v___x_4272_ = lean_mk_empty_array_with_capacity(v___x_4271_);
v___x_4273_ = lean_array_push(v___x_4272_, v___x_4270_);
v___x_4274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4269_);
lean_ctor_set(v___x_4274_, 1, v___x_4264_);
lean_ctor_set(v___x_4274_, 2, v___x_4273_);
return v___x_4274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4282_, lean_object* v_inst_4283_, lean_object* v_x_4284_){
_start:
{
lean_object* v_fst_4285_; lean_object* v_snd_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v_fst_4285_ = lean_ctor_get(v_x_4284_, 0);
lean_inc(v_fst_4285_);
v_snd_4286_ = lean_ctor_get(v_x_4284_, 1);
lean_inc(v_snd_4286_);
lean_dec_ref(v_x_4284_);
v___x_4287_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4288_ = lean_apply_1(v_inst_4282_, v_fst_4285_);
v___x_4289_ = lean_apply_1(v_inst_4283_, v_snd_4286_);
v___x_4290_ = lean_unsigned_to_nat(2u);
v___x_4291_ = lean_mk_empty_array_with_capacity(v___x_4290_);
v___x_4292_ = lean_array_push(v___x_4291_, v___x_4288_);
v___x_4293_ = lean_array_push(v___x_4292_, v___x_4289_);
v___x_4294_ = l_Lean_Syntax_mkCApp(v___x_4287_, v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4295_, lean_object* v_inst_4296_){
_start:
{
lean_object* v___f_4297_; 
v___f_4297_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4297_, 0, v_inst_4295_);
lean_closure_set(v___f_4297_, 1, v_inst_4296_);
return v___f_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4298_, lean_object* v_00_u03b2_4299_, lean_object* v_inst_4300_, lean_object* v_inst_4301_){
_start:
{
lean_object* v___f_4302_; 
v___f_4302_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4302_, 0, v_inst_4300_);
lean_closure_set(v___f_4302_, 1, v_inst_4301_);
return v___f_4302_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4309_ = l_Lean_mkCIdent(v___x_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4314_, lean_object* v_x_4315_){
_start:
{
if (lean_obj_tag(v_x_4315_) == 0)
{
lean_object* v___x_4316_; 
lean_dec_ref(v_inst_4314_);
v___x_4316_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4316_;
}
else
{
lean_object* v_head_4317_; lean_object* v_tail_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_head_4317_ = lean_ctor_get(v_x_4315_, 0);
lean_inc(v_head_4317_);
v_tail_4318_ = lean_ctor_get(v_x_4315_, 1);
lean_inc(v_tail_4318_);
lean_dec_ref(v_x_4315_);
v___x_4319_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4314_);
v___x_4320_ = lean_apply_1(v_inst_4314_, v_head_4317_);
v___x_4321_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4314_, v_tail_4318_);
v___x_4322_ = lean_unsigned_to_nat(2u);
v___x_4323_ = lean_mk_empty_array_with_capacity(v___x_4322_);
v___x_4324_ = lean_array_push(v___x_4323_, v___x_4320_);
v___x_4325_ = lean_array_push(v___x_4324_, v___x_4321_);
v___x_4326_ = l_Lean_Syntax_mkCApp(v___x_4319_, v___x_4325_);
return v___x_4326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4327_, lean_object* v_inst_4328_, lean_object* v_x_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4328_, v_x_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4331_, v_a_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4334_, lean_object* v_inst_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4335_, v_a_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4338_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4339_, 0, lean_box(0));
lean_closure_set(v___x_4339_, 1, v_inst_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4340_, lean_object* v_inst_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4342_, 0, lean_box(0));
lean_closure_set(v___x_4342_, 1, v_inst_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4345_, lean_object* v_xs_4346_, lean_object* v_i_4347_, lean_object* v_args_4348_){
_start:
{
lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4349_ = lean_array_get_size(v_xs_4346_);
v___x_4350_ = lean_nat_dec_lt(v_i_4347_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_dec(v_i_4347_);
lean_dec_ref(v_inst_4345_);
v___x_4351_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4352_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4353_ = l_Nat_reprFast(v___x_4349_);
v___x_4354_ = lean_string_append(v___x_4352_, v___x_4353_);
lean_dec_ref(v___x_4353_);
v___x_4355_ = l_Lean_Name_mkStr2(v___x_4351_, v___x_4354_);
v___x_4356_ = l_Lean_Syntax_mkCApp(v___x_4355_, v_args_4348_);
return v___x_4356_;
}
else
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = lean_nat_add(v_i_4347_, v___x_4357_);
v___x_4359_ = lean_array_fget_borrowed(v_xs_4346_, v_i_4347_);
lean_dec(v_i_4347_);
lean_inc_ref(v_inst_4345_);
lean_inc(v___x_4359_);
v___x_4360_ = lean_apply_1(v_inst_4345_, v___x_4359_);
v___x_4361_ = lean_array_push(v_args_4348_, v___x_4360_);
v_i_4347_ = v___x_4358_;
v_args_4348_ = v___x_4361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4363_, lean_object* v_xs_4364_, lean_object* v_i_4365_, lean_object* v_args_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4363_, v_xs_4364_, v_i_4365_, v_args_4366_);
lean_dec_ref(v_xs_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4368_, lean_object* v_inst_4369_, lean_object* v_xs_4370_, lean_object* v_i_4371_, lean_object* v_args_4372_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4369_, v_xs_4370_, v_i_4371_, v_args_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4374_, lean_object* v_inst_4375_, lean_object* v_xs_4376_, lean_object* v_i_4377_, lean_object* v_args_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4374_, v_inst_4375_, v_xs_4376_, v_i_4377_, v_args_4378_);
lean_dec_ref(v_xs_4376_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4384_, lean_object* v_xs_4385_){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4386_ = lean_array_get_size(v_xs_4385_);
v___x_4387_ = lean_unsigned_to_nat(8u);
v___x_4388_ = lean_nat_dec_le(v___x_4386_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4389_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4390_ = lean_array_to_list(v_xs_4385_);
v___x_4391_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4384_, v___x_4390_);
v___x_4392_ = lean_unsigned_to_nat(1u);
v___x_4393_ = lean_mk_empty_array_with_capacity(v___x_4392_);
v___x_4394_ = lean_array_push(v___x_4393_, v___x_4391_);
v___x_4395_ = l_Lean_Syntax_mkCApp(v___x_4389_, v___x_4394_);
return v___x_4395_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4398_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4384_, v_xs_4385_, v___x_4396_, v___x_4397_);
lean_dec_ref(v_xs_4385_);
return v___x_4398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4399_, lean_object* v_inst_4400_, lean_object* v_xs_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4400_, v_xs_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4403_, lean_object* v_xs_4404_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4403_, v_xs_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4406_, lean_object* v_inst_4407_, lean_object* v_xs_4408_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4407_, v_xs_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4410_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4411_, 0, lean_box(0));
lean_closure_set(v___x_4411_, 1, v_inst_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4412_, lean_object* v_inst_4413_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4414_, 0, lean_box(0));
lean_closure_set(v___x_4414_, 1, v_inst_4413_);
return v___x_4414_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4421_ = lean_mk_syntax_ident(v___x_4420_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4426_, lean_object* v_x_4427_){
_start:
{
if (lean_obj_tag(v_x_4427_) == 0)
{
lean_object* v___x_4428_; 
lean_dec_ref(v_inst_4426_);
v___x_4428_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4428_;
}
else
{
lean_object* v_val_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_val_4429_ = lean_ctor_get(v_x_4427_, 0);
lean_inc(v_val_4429_);
lean_dec_ref(v_x_4427_);
v___x_4430_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4431_ = lean_apply_1(v_inst_4426_, v_val_4429_);
v___x_4432_ = lean_unsigned_to_nat(1u);
v___x_4433_ = lean_mk_empty_array_with_capacity(v___x_4432_);
v___x_4434_ = lean_array_push(v___x_4433_, v___x_4431_);
v___x_4435_ = l_Lean_Syntax_mkCApp(v___x_4430_, v___x_4434_);
return v___x_4435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4436_){
_start:
{
lean_object* v___f_4437_; 
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4437_, 0, v_inst_4436_);
return v___f_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4438_, lean_object* v_inst_4439_){
_start:
{
lean_object* v___f_4440_; 
v___f_4440_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4440_, 0, v_inst_4439_);
return v___f_4440_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4441_, lean_object* v_k_4442_){
_start:
{
lean_object* v___x_4443_; uint8_t v___x_4444_; 
v___x_4443_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4444_ = lean_name_eq(v_k_4442_, v___x_4443_);
if (v___x_4444_ == 0)
{
uint8_t v___x_4445_; 
v___x_4445_ = 1;
return v___x_4445_;
}
else
{
return v___x_4441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4446_, lean_object* v_k_4447_){
_start:
{
uint8_t v___x_436__boxed_4448_; uint8_t v_res_4449_; lean_object* v_r_4450_; 
v___x_436__boxed_4448_ = lean_unbox(v___x_4446_);
v_res_4449_ = l_Lean_evalPrec___lam__0(v___x_436__boxed_4448_, v_k_4447_);
lean_dec(v_k_4447_);
v_r_4450_ = lean_box(v_res_4449_);
return v_r_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_methods_4455_; lean_object* v_quotContext_4456_; lean_object* v_currMacroScope_4457_; lean_object* v_currRecDepth_4458_; lean_object* v_maxRecDepth_4459_; lean_object* v_ref_4460_; uint8_t v___x_4461_; 
v_methods_4455_ = lean_ctor_get(v_a_4453_, 0);
v_quotContext_4456_ = lean_ctor_get(v_a_4453_, 1);
v_currMacroScope_4457_ = lean_ctor_get(v_a_4453_, 2);
v_currRecDepth_4458_ = lean_ctor_get(v_a_4453_, 3);
v_maxRecDepth_4459_ = lean_ctor_get(v_a_4453_, 4);
v_ref_4460_ = lean_ctor_get(v_a_4453_, 5);
v___x_4461_ = lean_nat_dec_eq(v_currRecDepth_4458_, v_maxRecDepth_4459_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; lean_object* v___f_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4462_ = lean_box(v___x_4461_);
v___f_4463_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4463_, 0, v___x_4462_);
v___x_4464_ = lean_unsigned_to_nat(1u);
v___x_4465_ = lean_nat_add(v_currRecDepth_4458_, v___x_4464_);
lean_inc(v_ref_4460_);
lean_inc(v_maxRecDepth_4459_);
lean_inc(v_currMacroScope_4457_);
lean_inc(v_quotContext_4456_);
lean_inc(v_methods_4455_);
v___x_4466_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4466_, 0, v_methods_4455_);
lean_ctor_set(v___x_4466_, 1, v_quotContext_4456_);
lean_ctor_set(v___x_4466_, 2, v_currMacroScope_4457_);
lean_ctor_set(v___x_4466_, 3, v___x_4465_);
lean_ctor_set(v___x_4466_, 4, v_maxRecDepth_4459_);
lean_ctor_set(v___x_4466_, 5, v_ref_4460_);
lean_inc_ref(v___x_4466_);
v___x_4467_ = l_Lean_expandMacros(v_stx_4452_, v___f_4463_, v___x_4466_, v_a_4454_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4481_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_a_4469_ = lean_ctor_get(v___x_4467_, 1);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4471_ = v___x_4467_;
v_isShared_4472_ = v_isSharedCheck_4481_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4481_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; uint8_t v___x_4474_; 
v___x_4473_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4468_);
v___x_4474_ = l_Lean_Syntax_isOfKind(v_a_4468_, v___x_4473_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_del_object(v___x_4471_);
v___x_4475_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4476_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4468_, v___x_4475_, v___x_4466_, v_a_4469_);
lean_dec_ref(v___x_4466_);
lean_dec(v_a_4468_);
return v___x_4476_;
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
lean_dec_ref(v___x_4466_);
v___x_4477_ = l_Lean_TSyntax_getNat(v_a_4468_);
lean_dec(v_a_4468_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4477_);
v___x_4479_ = v___x_4471_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_a_4469_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref(v___x_4466_);
v_a_4482_ = lean_ctor_get(v___x_4467_, 0);
v_a_4483_ = lean_ctor_get(v___x_4467_, 1);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4467_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_inc(v_a_4482_);
lean_dec(v___x_4467_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4482_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v_stx_4452_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
lean_ctor_set(v___x_4493_, 1, v_a_4454_);
return v___x_4493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_evalPrec(v_stx_4494_, v_a_4495_, v_a_4496_);
lean_dec_ref(v_a_4495_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_methods_4502_; lean_object* v_quotContext_4503_; lean_object* v_currMacroScope_4504_; lean_object* v_currRecDepth_4505_; lean_object* v_maxRecDepth_4506_; lean_object* v_ref_4507_; uint8_t v___x_4508_; 
v_methods_4502_ = lean_ctor_get(v_a_4500_, 0);
v_quotContext_4503_ = lean_ctor_get(v_a_4500_, 1);
v_currMacroScope_4504_ = lean_ctor_get(v_a_4500_, 2);
v_currRecDepth_4505_ = lean_ctor_get(v_a_4500_, 3);
v_maxRecDepth_4506_ = lean_ctor_get(v_a_4500_, 4);
v_ref_4507_ = lean_ctor_get(v_a_4500_, 5);
v___x_4508_ = lean_nat_dec_eq(v_currRecDepth_4505_, v_maxRecDepth_4506_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___f_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4509_ = lean_box(v___x_4508_);
v___f_4510_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4510_, 0, v___x_4509_);
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = lean_nat_add(v_currRecDepth_4505_, v___x_4511_);
lean_inc(v_ref_4507_);
lean_inc(v_maxRecDepth_4506_);
lean_inc(v_currMacroScope_4504_);
lean_inc(v_quotContext_4503_);
lean_inc(v_methods_4502_);
v___x_4513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4513_, 0, v_methods_4502_);
lean_ctor_set(v___x_4513_, 1, v_quotContext_4503_);
lean_ctor_set(v___x_4513_, 2, v_currMacroScope_4504_);
lean_ctor_set(v___x_4513_, 3, v___x_4512_);
lean_ctor_set(v___x_4513_, 4, v_maxRecDepth_4506_);
lean_ctor_set(v___x_4513_, 5, v_ref_4507_);
lean_inc_ref(v___x_4513_);
v___x_4514_ = l_Lean_expandMacros(v_stx_4499_, v___f_4510_, v___x_4513_, v_a_4501_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4528_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
v_a_4516_ = lean_ctor_get(v___x_4514_, 1);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4518_ = v___x_4514_;
v_isShared_4519_ = v_isSharedCheck_4528_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_inc(v_a_4515_);
lean_dec(v___x_4514_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4528_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4515_);
v___x_4521_ = l_Lean_Syntax_isOfKind(v_a_4515_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
lean_del_object(v___x_4518_);
v___x_4522_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4523_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4515_, v___x_4522_, v___x_4513_, v_a_4516_);
lean_dec_ref(v___x_4513_);
lean_dec(v_a_4515_);
return v___x_4523_;
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4526_; 
lean_dec_ref(v___x_4513_);
v___x_4524_ = l_Lean_TSyntax_getNat(v_a_4515_);
lean_dec(v_a_4515_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 0, v___x_4524_);
v___x_4526_ = v___x_4518_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_a_4516_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec_ref(v___x_4513_);
v_a_4529_ = lean_ctor_get(v___x_4514_, 0);
v_a_4530_ = lean_ctor_get(v___x_4514_, 1);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4514_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_inc(v_a_4529_);
lean_dec(v___x_4514_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4529_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4539_, 0, v_stx_4499_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
lean_ctor_set(v___x_4540_, 1, v_a_4501_);
return v___x_4540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_evalPrio(v_stx_4541_, v_a_4542_, v_a_4543_);
lean_dec_ref(v_a_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
if (lean_obj_tag(v_x_4545_) == 0)
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = lean_unsigned_to_nat(1000u);
v___x_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
lean_ctor_set(v___x_4549_, 1, v_a_4547_);
return v___x_4549_;
}
else
{
lean_object* v_val_4550_; lean_object* v___x_4551_; 
v_val_4550_ = lean_ctor_get(v_x_4545_, 0);
lean_inc(v_val_4550_);
lean_dec_ref(v_x_4545_);
v___x_4551_ = l_Lean_evalPrio(v_val_4550_, v_a_4546_, v_a_4547_);
return v___x_4551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_evalOptPrio(v_x_4552_, v_a_4553_, v_a_4554_);
lean_dec_ref(v_a_4553_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4556_, lean_object* v_x1_4557_, lean_object* v_x2_4558_){
_start:
{
lean_object* v_fst_4559_; uint8_t v___x_4560_; 
v_fst_4559_ = lean_ctor_get(v_x1_4557_, 0);
v___x_4560_ = lean_unbox(v_fst_4559_);
if (v___x_4560_ == 0)
{
lean_object* v_snd_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v_x2_4558_);
v_snd_4561_ = lean_ctor_get(v_x1_4557_, 1);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_x1_4557_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; 
v_unused_4570_ = lean_ctor_get(v_x1_4557_, 0);
lean_dec(v_unused_4570_);
v___x_4563_ = v_x1_4557_;
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_snd_4561_);
lean_dec(v_x1_4557_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4565_ = lean_box(v___x_4556_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4565_);
v___x_4567_ = v___x_4563_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v_snd_4561_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
else
{
lean_object* v_snd_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4581_; 
v_snd_4571_ = lean_ctor_get(v_x1_4557_, 1);
v_isSharedCheck_4581_ = !lean_is_exclusive(v_x1_4557_);
if (v_isSharedCheck_4581_ == 0)
{
lean_object* v_unused_4582_; 
v_unused_4582_ = lean_ctor_get(v_x1_4557_, 0);
lean_dec(v_unused_4582_);
v___x_4573_ = v_x1_4557_;
v_isShared_4574_ = v_isSharedCheck_4581_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_snd_4571_);
lean_dec(v_x1_4557_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4581_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
uint8_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4579_; 
v___x_4575_ = 0;
v___x_4576_ = lean_array_push(v_snd_4571_, v_x2_4558_);
v___x_4577_ = lean_box(v___x_4575_);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 1, v___x_4576_);
lean_ctor_set(v___x_4573_, 0, v___x_4577_);
v___x_4579_ = v___x_4573_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4580_, 1, v___x_4576_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4583_, lean_object* v_x1_4584_, lean_object* v_x2_4585_){
_start:
{
uint8_t v___x_96__boxed_4586_; lean_object* v_res_4587_; 
v___x_96__boxed_4586_ = lean_unbox(v___x_4583_);
v_res_4587_ = l_Array_getSepElems___redArg___lam__0(v___x_96__boxed_4586_, v_x1_4584_, v_x2_4585_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4609_){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4610_ = lean_unsigned_to_nat(0u);
v___x_4611_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4612_ = lean_array_get_size(v_as_4609_);
v___x_4613_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4614_ = lean_nat_dec_lt(v___x_4610_, v___x_4612_);
if (v___x_4614_ == 0)
{
lean_dec_ref(v_as_4609_);
return v___x_4611_;
}
else
{
lean_object* v___x_4615_; lean_object* v___f_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4615_ = lean_box(v___x_4614_);
v___f_4616_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4616_, 0, v___x_4615_);
v___x_4617_ = lean_box(v___x_4614_);
v___x_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
lean_ctor_set(v___x_4618_, 1, v___x_4611_);
v___x_4619_ = lean_nat_dec_le(v___x_4612_, v___x_4612_);
if (v___x_4619_ == 0)
{
if (v___x_4614_ == 0)
{
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___f_4616_);
lean_dec_ref(v_as_4609_);
return v___x_4611_;
}
else
{
size_t v___x_4620_; size_t v___x_4621_; lean_object* v___x_4622_; lean_object* v_snd_4623_; 
v___x_4620_ = ((size_t)0ULL);
v___x_4621_ = lean_usize_of_nat(v___x_4612_);
v___x_4622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4613_, v___f_4616_, v_as_4609_, v___x_4620_, v___x_4621_, v___x_4618_);
v_snd_4623_ = lean_ctor_get(v___x_4622_, 1);
lean_inc(v_snd_4623_);
lean_dec(v___x_4622_);
return v_snd_4623_;
}
}
else
{
size_t v___x_4624_; size_t v___x_4625_; lean_object* v___x_4626_; lean_object* v_snd_4627_; 
v___x_4624_ = ((size_t)0ULL);
v___x_4625_ = lean_usize_of_nat(v___x_4612_);
v___x_4626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4613_, v___f_4616_, v_as_4609_, v___x_4624_, v___x_4625_, v___x_4618_);
v_snd_4627_ = lean_ctor_get(v___x_4626_, 1);
lean_inc(v_snd_4627_);
lean_dec(v___x_4626_);
return v_snd_4627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4628_, lean_object* v_as_4629_){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4630_ = lean_unsigned_to_nat(0u);
v___x_4631_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4632_ = lean_array_get_size(v_as_4629_);
v___x_4633_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4634_ = lean_nat_dec_lt(v___x_4630_, v___x_4632_);
if (v___x_4634_ == 0)
{
lean_dec_ref(v_as_4629_);
return v___x_4631_;
}
else
{
lean_object* v___x_4635_; lean_object* v___f_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v___x_4635_ = lean_box(v___x_4634_);
v___f_4636_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4636_, 0, v___x_4635_);
v___x_4637_ = lean_box(v___x_4634_);
v___x_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
lean_ctor_set(v___x_4638_, 1, v___x_4631_);
v___x_4639_ = lean_nat_dec_le(v___x_4632_, v___x_4632_);
if (v___x_4639_ == 0)
{
if (v___x_4634_ == 0)
{
lean_dec_ref(v___x_4638_);
lean_dec_ref(v___f_4636_);
lean_dec_ref(v_as_4629_);
return v___x_4631_;
}
else
{
size_t v___x_4640_; size_t v___x_4641_; lean_object* v___x_4642_; lean_object* v_snd_4643_; 
v___x_4640_ = ((size_t)0ULL);
v___x_4641_ = lean_usize_of_nat(v___x_4632_);
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4633_, v___f_4636_, v_as_4629_, v___x_4640_, v___x_4641_, v___x_4638_);
v_snd_4643_ = lean_ctor_get(v___x_4642_, 1);
lean_inc(v_snd_4643_);
lean_dec(v___x_4642_);
return v_snd_4643_;
}
}
else
{
size_t v___x_4644_; size_t v___x_4645_; lean_object* v___x_4646_; lean_object* v_snd_4647_; 
v___x_4644_ = ((size_t)0ULL);
v___x_4645_ = lean_usize_of_nat(v___x_4632_);
v___x_4646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4633_, v___f_4636_, v_as_4629_, v___x_4644_, v___x_4645_, v___x_4638_);
v_snd_4647_ = lean_ctor_get(v___x_4646_, 1);
lean_inc(v_snd_4647_);
lean_dec(v___x_4646_);
return v_snd_4647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4648_, lean_object* v_inst_4649_, lean_object* v_a_4650_, lean_object* v_p_4651_, lean_object* v_acc_4652_, lean_object* v_stx_4653_, uint8_t v_____do__lift_4654_){
_start:
{
if (v_____do__lift_4654_ == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
lean_dec(v_stx_4653_);
v___x_4663_ = lean_unsigned_to_nat(2u);
v___x_4664_ = lean_nat_add(v_i_4648_, v___x_4663_);
v___x_4665_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4649_, v_a_4650_, v_p_4651_, v___x_4664_, v_acc_4652_);
return v___x_4665_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4666_ = lean_array_get_size(v_acc_4652_);
v___x_4667_ = lean_unsigned_to_nat(0u);
v___x_4668_ = lean_nat_dec_eq(v___x_4666_, v___x_4667_);
if (v___x_4668_ == 0)
{
uint8_t v___x_4669_; 
v___x_4669_ = lean_nat_dec_eq(v_i_4648_, v___x_4667_);
if (v___x_4669_ == 0)
{
goto v___jp_4655_;
}
else
{
if (v___x_4668_ == 0)
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4670_ = lean_unsigned_to_nat(2u);
v___x_4671_ = lean_nat_add(v_i_4648_, v___x_4670_);
v___x_4672_ = lean_array_push(v_acc_4652_, v_stx_4653_);
v___x_4673_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4649_, v_a_4650_, v_p_4651_, v___x_4671_, v___x_4672_);
return v___x_4673_;
}
else
{
goto v___jp_4655_;
}
}
}
else
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4674_ = lean_unsigned_to_nat(2u);
v___x_4675_ = lean_nat_add(v_i_4648_, v___x_4674_);
v___x_4676_ = lean_array_push(v_acc_4652_, v_stx_4653_);
v___x_4677_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4649_, v_a_4650_, v_p_4651_, v___x_4675_, v___x_4676_);
return v___x_4677_;
}
}
v___jp_4655_:
{
lean_object* v___x_4656_; lean_object* v_sepStx_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4656_ = lean_nat_pred(v_i_4648_);
v_sepStx_4657_ = lean_array_fget_borrowed(v_a_4650_, v___x_4656_);
lean_dec(v___x_4656_);
v___x_4658_ = lean_unsigned_to_nat(2u);
v___x_4659_ = lean_nat_add(v_i_4648_, v___x_4658_);
lean_inc(v_sepStx_4657_);
v___x_4660_ = lean_array_push(v_acc_4652_, v_sepStx_4657_);
v___x_4661_ = lean_array_push(v___x_4660_, v_stx_4653_);
v___x_4662_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4649_, v_a_4650_, v_p_4651_, v___x_4659_, v___x_4661_);
return v___x_4662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4678_, lean_object* v_inst_4679_, lean_object* v_a_4680_, lean_object* v_p_4681_, lean_object* v_acc_4682_, lean_object* v_stx_4683_, lean_object* v_____do__lift_4684_){
_start:
{
uint8_t v_____do__lift_284__boxed_4685_; lean_object* v_res_4686_; 
v_____do__lift_284__boxed_4685_ = lean_unbox(v_____do__lift_4684_);
v_res_4686_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4678_, v_inst_4679_, v_a_4680_, v_p_4681_, v_acc_4682_, v_stx_4683_, v_____do__lift_284__boxed_4685_);
lean_dec(v_i_4678_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4687_, lean_object* v_a_4688_, lean_object* v_p_4689_, lean_object* v_i_4690_, lean_object* v_acc_4691_){
_start:
{
lean_object* v___x_4692_; uint8_t v___x_4693_; 
v___x_4692_ = lean_array_get_size(v_a_4688_);
v___x_4693_ = lean_nat_dec_lt(v_i_4690_, v___x_4692_);
if (v___x_4693_ == 0)
{
lean_object* v_toApplicative_4694_; lean_object* v_toPure_4695_; lean_object* v___x_4696_; 
lean_dec(v_i_4690_);
lean_dec(v_p_4689_);
lean_dec_ref(v_a_4688_);
v_toApplicative_4694_ = lean_ctor_get(v_inst_4687_, 0);
lean_inc_ref(v_toApplicative_4694_);
lean_dec_ref(v_inst_4687_);
v_toPure_4695_ = lean_ctor_get(v_toApplicative_4694_, 1);
lean_inc(v_toPure_4695_);
lean_dec_ref(v_toApplicative_4694_);
v___x_4696_ = lean_apply_2(v_toPure_4695_, lean_box(0), v_acc_4691_);
return v___x_4696_;
}
else
{
lean_object* v_toBind_4697_; lean_object* v_stx_4698_; lean_object* v___f_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_toBind_4697_ = lean_ctor_get(v_inst_4687_, 1);
lean_inc(v_toBind_4697_);
v_stx_4698_ = lean_array_fget(v_a_4688_, v_i_4690_);
lean_inc(v_stx_4698_);
lean_inc(v_p_4689_);
v___f_4699_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4699_, 0, v_i_4690_);
lean_closure_set(v___f_4699_, 1, v_inst_4687_);
lean_closure_set(v___f_4699_, 2, v_a_4688_);
lean_closure_set(v___f_4699_, 3, v_p_4689_);
lean_closure_set(v___f_4699_, 4, v_acc_4691_);
lean_closure_set(v___f_4699_, 5, v_stx_4698_);
v___x_4700_ = lean_apply_1(v_p_4689_, v_stx_4698_);
v___x_4701_ = lean_apply_4(v_toBind_4697_, lean_box(0), lean_box(0), v___x_4700_, v___f_4699_);
return v___x_4701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4702_, lean_object* v_inst_4703_, lean_object* v_a_4704_, lean_object* v_p_4705_, lean_object* v_i_4706_, lean_object* v_acc_4707_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4703_, v_a_4704_, v_p_4705_, v_i_4706_, v_acc_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4709_, lean_object* v_a_4710_, lean_object* v_p_4711_){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4712_ = lean_unsigned_to_nat(0u);
v___x_4713_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4714_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4709_, v_a_4710_, v_p_4711_, v___x_4712_, v___x_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4715_, lean_object* v_inst_4716_, lean_object* v_a_4717_, lean_object* v_p_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Array_filterSepElemsM___redArg(v_inst_4716_, v_a_4717_, v_p_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4720_, lean_object* v_x_4721_){
_start:
{
lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4722_ = lean_apply_1(v_p_4720_, v_x_4721_);
v___x_4723_ = lean_unbox(v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4724_, lean_object* v_x_4725_){
_start:
{
uint8_t v_res_4726_; lean_object* v_r_4727_; 
v_res_4726_ = l_Array_filterSepElems___lam__0(v_p_4724_, v_x_4725_);
v_r_4727_ = lean_box(v_res_4726_);
return v_r_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4728_, lean_object* v_p_4729_, lean_object* v_i_4730_, lean_object* v_acc_4731_){
_start:
{
lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4732_ = lean_array_get_size(v_a_4728_);
v___x_4733_ = lean_nat_dec_lt(v_i_4730_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_dec(v_i_4730_);
lean_dec_ref(v_p_4729_);
return v_acc_4731_;
}
else
{
lean_object* v_stx_4734_; lean_object* v___x_4743_; uint8_t v___x_4744_; 
v_stx_4734_ = lean_array_fget_borrowed(v_a_4728_, v_i_4730_);
lean_inc_ref(v_p_4729_);
lean_inc(v_stx_4734_);
v___x_4743_ = lean_apply_1(v_p_4729_, v_stx_4734_);
v___x_4744_ = lean_unbox(v___x_4743_);
if (v___x_4744_ == 0)
{
lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = lean_unsigned_to_nat(2u);
v___x_4746_ = lean_nat_add(v_i_4730_, v___x_4745_);
lean_dec(v_i_4730_);
v_i_4730_ = v___x_4746_;
goto _start;
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; 
v___x_4748_ = lean_array_get_size(v_acc_4731_);
v___x_4749_ = lean_unsigned_to_nat(0u);
v___x_4750_ = lean_nat_dec_eq(v___x_4748_, v___x_4749_);
if (v___x_4750_ == 0)
{
uint8_t v___x_4751_; 
v___x_4751_ = lean_nat_dec_eq(v_i_4730_, v___x_4749_);
if (v___x_4751_ == 0)
{
goto v___jp_4735_;
}
else
{
if (v___x_4750_ == 0)
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = lean_unsigned_to_nat(2u);
v___x_4753_ = lean_nat_add(v_i_4730_, v___x_4752_);
lean_dec(v_i_4730_);
lean_inc(v_stx_4734_);
v___x_4754_ = lean_array_push(v_acc_4731_, v_stx_4734_);
v_i_4730_ = v___x_4753_;
v_acc_4731_ = v___x_4754_;
goto _start;
}
else
{
goto v___jp_4735_;
}
}
}
else
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4756_ = lean_unsigned_to_nat(2u);
v___x_4757_ = lean_nat_add(v_i_4730_, v___x_4756_);
lean_dec(v_i_4730_);
lean_inc(v_stx_4734_);
v___x_4758_ = lean_array_push(v_acc_4731_, v_stx_4734_);
v_i_4730_ = v___x_4757_;
v_acc_4731_ = v___x_4758_;
goto _start;
}
}
v___jp_4735_:
{
lean_object* v___x_4736_; lean_object* v_sepStx_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4736_ = lean_nat_pred(v_i_4730_);
v_sepStx_4737_ = lean_array_fget_borrowed(v_a_4728_, v___x_4736_);
lean_dec(v___x_4736_);
v___x_4738_ = lean_unsigned_to_nat(2u);
v___x_4739_ = lean_nat_add(v_i_4730_, v___x_4738_);
lean_dec(v_i_4730_);
lean_inc(v_sepStx_4737_);
v___x_4740_ = lean_array_push(v_acc_4731_, v_sepStx_4737_);
lean_inc(v_stx_4734_);
v___x_4741_ = lean_array_push(v___x_4740_, v_stx_4734_);
v_i_4730_ = v___x_4739_;
v_acc_4731_ = v___x_4741_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4760_, lean_object* v_p_4761_, lean_object* v_i_4762_, lean_object* v_acc_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4760_, v_p_4761_, v_i_4762_, v_acc_4763_);
lean_dec_ref(v_a_4760_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4765_, lean_object* v_p_4766_){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4767_ = lean_unsigned_to_nat(0u);
v___x_4768_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4769_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4765_, v_p_4766_, v___x_4767_, v___x_4768_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4770_, lean_object* v_p_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4770_, v_p_4771_);
lean_dec_ref(v_a_4770_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4773_, lean_object* v_p_4774_){
_start:
{
lean_object* v___f_4775_; lean_object* v___x_4776_; 
v___f_4775_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4775_, 0, v_p_4774_);
v___x_4776_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4773_, v___f_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4777_, lean_object* v_p_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Array_filterSepElems(v_a_4777_, v_p_4778_);
lean_dec_ref(v_a_4777_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4780_, lean_object* v_acc_4781_, lean_object* v_inst_4782_, lean_object* v_a_4783_, lean_object* v_f_4784_, lean_object* v_stx_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4780_, v_acc_4781_, v_inst_4782_, v_a_4783_, v_f_4784_, v_stx_4785_);
lean_dec(v_i_4780_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4787_, lean_object* v_a_4788_, lean_object* v_f_4789_, lean_object* v_i_4790_, lean_object* v_acc_4791_){
_start:
{
lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4792_ = lean_array_get_size(v_a_4788_);
v___x_4793_ = lean_nat_dec_lt(v_i_4790_, v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v_toApplicative_4794_; lean_object* v_toPure_4795_; lean_object* v___x_4796_; 
lean_dec(v_i_4790_);
lean_dec(v_f_4789_);
lean_dec_ref(v_a_4788_);
v_toApplicative_4794_ = lean_ctor_get(v_inst_4787_, 0);
lean_inc_ref(v_toApplicative_4794_);
lean_dec_ref(v_inst_4787_);
v_toPure_4795_ = lean_ctor_get(v_toApplicative_4794_, 1);
lean_inc(v_toPure_4795_);
lean_dec_ref(v_toApplicative_4794_);
v___x_4796_ = lean_apply_2(v_toPure_4795_, lean_box(0), v_acc_4791_);
return v___x_4796_;
}
else
{
lean_object* v_stx_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; uint8_t v___x_4801_; 
v_stx_4797_ = lean_array_fget_borrowed(v_a_4788_, v_i_4790_);
v___x_4798_ = lean_unsigned_to_nat(2u);
v___x_4799_ = lean_nat_mod(v_i_4790_, v___x_4798_);
v___x_4800_ = lean_unsigned_to_nat(0u);
v___x_4801_ = lean_nat_dec_eq(v___x_4799_, v___x_4800_);
lean_dec(v___x_4799_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = lean_unsigned_to_nat(1u);
v___x_4803_ = lean_nat_add(v_i_4790_, v___x_4802_);
lean_dec(v_i_4790_);
lean_inc(v_stx_4797_);
v___x_4804_ = lean_array_push(v_acc_4791_, v_stx_4797_);
v_i_4790_ = v___x_4803_;
v_acc_4791_ = v___x_4804_;
goto _start;
}
else
{
lean_object* v_toBind_4806_; lean_object* v___f_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
lean_inc(v_stx_4797_);
v_toBind_4806_ = lean_ctor_get(v_inst_4787_, 1);
lean_inc(v_toBind_4806_);
lean_inc(v_f_4789_);
v___f_4807_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4807_, 0, v_i_4790_);
lean_closure_set(v___f_4807_, 1, v_acc_4791_);
lean_closure_set(v___f_4807_, 2, v_inst_4787_);
lean_closure_set(v___f_4807_, 3, v_a_4788_);
lean_closure_set(v___f_4807_, 4, v_f_4789_);
v___x_4808_ = lean_apply_1(v_f_4789_, v_stx_4797_);
v___x_4809_ = lean_apply_4(v_toBind_4806_, lean_box(0), lean_box(0), v___x_4808_, v___f_4807_);
return v___x_4809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4810_, lean_object* v_acc_4811_, lean_object* v_inst_4812_, lean_object* v_a_4813_, lean_object* v_f_4814_, lean_object* v_stx_4815_){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4816_ = lean_unsigned_to_nat(1u);
v___x_4817_ = lean_nat_add(v_i_4810_, v___x_4816_);
v___x_4818_ = lean_array_push(v_acc_4811_, v_stx_4815_);
v___x_4819_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4812_, v_a_4813_, v_f_4814_, v___x_4817_, v___x_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4820_, lean_object* v_inst_4821_, lean_object* v_a_4822_, lean_object* v_f_4823_, lean_object* v_i_4824_, lean_object* v_acc_4825_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4821_, v_a_4822_, v_f_4823_, v_i_4824_, v_acc_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4827_, lean_object* v_a_4828_, lean_object* v_f_4829_){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4832_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4827_, v_a_4828_, v_f_4829_, v___x_4830_, v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4833_, lean_object* v_inst_4834_, lean_object* v_a_4835_, lean_object* v_f_4836_){
_start:
{
lean_object* v___x_4837_; 
v___x_4837_ = l_Array_mapSepElemsM___redArg(v_inst_4834_, v_a_4835_, v_f_4836_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4838_, lean_object* v_x_4839_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_apply_1(v_f_4838_, v_x_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4841_, lean_object* v_f_4842_, lean_object* v_i_4843_, lean_object* v_acc_4844_){
_start:
{
lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4845_ = lean_array_get_size(v_a_4841_);
v___x_4846_ = lean_nat_dec_lt(v_i_4843_, v___x_4845_);
if (v___x_4846_ == 0)
{
lean_dec(v_i_4843_);
lean_dec_ref(v_f_4842_);
return v_acc_4844_;
}
else
{
lean_object* v_stx_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; 
v_stx_4847_ = lean_array_fget_borrowed(v_a_4841_, v_i_4843_);
v___x_4848_ = lean_unsigned_to_nat(2u);
v___x_4849_ = lean_nat_mod(v_i_4843_, v___x_4848_);
v___x_4850_ = lean_unsigned_to_nat(0u);
v___x_4851_ = lean_nat_dec_eq(v___x_4849_, v___x_4850_);
lean_dec(v___x_4849_);
if (v___x_4851_ == 0)
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4852_ = lean_unsigned_to_nat(1u);
v___x_4853_ = lean_nat_add(v_i_4843_, v___x_4852_);
lean_dec(v_i_4843_);
lean_inc(v_stx_4847_);
v___x_4854_ = lean_array_push(v_acc_4844_, v_stx_4847_);
v_i_4843_ = v___x_4853_;
v_acc_4844_ = v___x_4854_;
goto _start;
}
else
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
lean_inc_ref(v_f_4842_);
lean_inc(v_stx_4847_);
v___x_4856_ = lean_apply_1(v_f_4842_, v_stx_4847_);
v___x_4857_ = lean_unsigned_to_nat(1u);
v___x_4858_ = lean_nat_add(v_i_4843_, v___x_4857_);
lean_dec(v_i_4843_);
v___x_4859_ = lean_array_push(v_acc_4844_, v___x_4856_);
v_i_4843_ = v___x_4858_;
v_acc_4844_ = v___x_4859_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4861_, lean_object* v_f_4862_, lean_object* v_i_4863_, lean_object* v_acc_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4861_, v_f_4862_, v_i_4863_, v_acc_4864_);
lean_dec_ref(v_a_4861_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4866_, lean_object* v_f_4867_){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4868_ = lean_unsigned_to_nat(0u);
v___x_4869_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4870_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4866_, v_f_4867_, v___x_4868_, v___x_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4871_, lean_object* v_f_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4871_, v_f_4872_);
lean_dec_ref(v_a_4871_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4874_, lean_object* v_f_4875_){
_start:
{
lean_object* v___f_4876_; lean_object* v___x_4877_; 
v___f_4876_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4876_, 0, v_f_4875_);
v___x_4877_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4874_, v___f_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4878_, lean_object* v_f_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Array_mapSepElems(v_a_4878_, v_f_4879_);
lean_dec_ref(v_a_4878_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4881_, size_t v_i_4882_, size_t v_stop_4883_, lean_object* v_b_4884_){
_start:
{
lean_object* v___y_4886_; uint8_t v___x_4890_; 
v___x_4890_ = lean_usize_dec_eq(v_i_4882_, v_stop_4883_);
if (v___x_4890_ == 0)
{
lean_object* v_fst_4891_; uint8_t v___x_4892_; 
v_fst_4891_ = lean_ctor_get(v_b_4884_, 0);
v___x_4892_ = lean_unbox(v_fst_4891_);
if (v___x_4892_ == 0)
{
lean_object* v_snd_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4902_; 
v_snd_4893_ = lean_ctor_get(v_b_4884_, 1);
v_isSharedCheck_4902_ = !lean_is_exclusive(v_b_4884_);
if (v_isSharedCheck_4902_ == 0)
{
lean_object* v_unused_4903_; 
v_unused_4903_ = lean_ctor_get(v_b_4884_, 0);
lean_dec(v_unused_4903_);
v___x_4895_ = v_b_4884_;
v_isShared_4896_ = v_isSharedCheck_4902_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_snd_4893_);
lean_dec(v_b_4884_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4902_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
uint8_t v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4900_; 
v___x_4897_ = 1;
v___x_4898_ = lean_box(v___x_4897_);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 0, v___x_4898_);
v___x_4900_ = v___x_4895_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4898_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_snd_4893_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
v___y_4886_ = v___x_4900_;
goto v___jp_4885_;
}
}
}
else
{
lean_object* v_snd_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4914_; 
v_snd_4904_ = lean_ctor_get(v_b_4884_, 1);
v_isSharedCheck_4914_ = !lean_is_exclusive(v_b_4884_);
if (v_isSharedCheck_4914_ == 0)
{
lean_object* v_unused_4915_; 
v_unused_4915_ = lean_ctor_get(v_b_4884_, 0);
lean_dec(v_unused_4915_);
v___x_4906_ = v_b_4884_;
v_isShared_4907_ = v_isSharedCheck_4914_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_snd_4904_);
lean_dec(v_b_4884_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4914_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4912_; 
v___x_4908_ = lean_array_uget_borrowed(v_as_4881_, v_i_4882_);
lean_inc(v___x_4908_);
v___x_4909_ = lean_array_push(v_snd_4904_, v___x_4908_);
v___x_4910_ = lean_box(v___x_4890_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 1, v___x_4909_);
lean_ctor_set(v___x_4906_, 0, v___x_4910_);
v___x_4912_ = v___x_4906_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v___x_4909_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
v___y_4886_ = v___x_4912_;
goto v___jp_4885_;
}
}
}
}
else
{
return v_b_4884_;
}
v___jp_4885_:
{
size_t v___x_4887_; size_t v___x_4888_; 
v___x_4887_ = ((size_t)1ULL);
v___x_4888_ = lean_usize_add(v_i_4882_, v___x_4887_);
v_i_4882_ = v___x_4888_;
v_b_4884_ = v___y_4886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4916_, lean_object* v_i_4917_, lean_object* v_stop_4918_, lean_object* v_b_4919_){
_start:
{
size_t v_i_boxed_4920_; size_t v_stop_boxed_4921_; lean_object* v_res_4922_; 
v_i_boxed_4920_ = lean_unbox_usize(v_i_4917_);
lean_dec(v_i_4917_);
v_stop_boxed_4921_ = lean_unbox_usize(v_stop_4918_);
lean_dec(v_stop_4918_);
v_res_4922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4916_, v_i_boxed_4920_, v_stop_boxed_4921_, v_b_4919_);
lean_dec_ref(v_as_4916_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4923_){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
v___x_4924_ = lean_unsigned_to_nat(0u);
v___x_4925_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4926_ = lean_array_get_size(v_sa_4923_);
v___x_4927_ = lean_nat_dec_lt(v___x_4924_, v___x_4926_);
if (v___x_4927_ == 0)
{
return v___x_4925_;
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; uint8_t v___x_4930_; 
v___x_4928_ = lean_box(v___x_4927_);
v___x_4929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
lean_ctor_set(v___x_4929_, 1, v___x_4925_);
v___x_4930_ = lean_nat_dec_le(v___x_4926_, v___x_4926_);
if (v___x_4930_ == 0)
{
if (v___x_4927_ == 0)
{
lean_dec_ref(v___x_4929_);
return v___x_4925_;
}
else
{
size_t v___x_4931_; size_t v___x_4932_; lean_object* v___x_4933_; lean_object* v_snd_4934_; 
v___x_4931_ = ((size_t)0ULL);
v___x_4932_ = lean_usize_of_nat(v___x_4926_);
v___x_4933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4923_, v___x_4931_, v___x_4932_, v___x_4929_);
v_snd_4934_ = lean_ctor_get(v___x_4933_, 1);
lean_inc(v_snd_4934_);
lean_dec_ref(v___x_4933_);
return v_snd_4934_;
}
}
else
{
size_t v___x_4935_; size_t v___x_4936_; lean_object* v___x_4937_; lean_object* v_snd_4938_; 
v___x_4935_ = ((size_t)0ULL);
v___x_4936_ = lean_usize_of_nat(v___x_4926_);
v___x_4937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4923_, v___x_4935_, v___x_4936_, v___x_4929_);
v_snd_4938_ = lean_ctor_get(v___x_4937_, 1);
lean_inc(v_snd_4938_);
lean_dec_ref(v___x_4937_);
return v_snd_4938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4939_);
lean_dec_ref(v_sa_4939_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4941_, lean_object* v_sa_4942_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4944_, lean_object* v_sa_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Syntax_SepArray_getElems(v_sep_4944_, v_sa_4945_);
lean_dec_ref(v_sa_4945_);
lean_dec_ref(v_sep_4944_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4947_){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4948_ = lean_unsigned_to_nat(0u);
v___x_4949_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4950_ = lean_array_get_size(v_sa_4947_);
v___x_4951_ = lean_nat_dec_lt(v___x_4948_, v___x_4950_);
if (v___x_4951_ == 0)
{
return v___x_4949_;
}
else
{
lean_object* v___x_4952_; lean_object* v___x_4953_; uint8_t v___x_4954_; 
v___x_4952_ = lean_box(v___x_4951_);
v___x_4953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4952_);
lean_ctor_set(v___x_4953_, 1, v___x_4949_);
v___x_4954_ = lean_nat_dec_le(v___x_4950_, v___x_4950_);
if (v___x_4954_ == 0)
{
if (v___x_4951_ == 0)
{
lean_dec_ref(v___x_4953_);
return v___x_4949_;
}
else
{
size_t v___x_4955_; size_t v___x_4956_; lean_object* v___x_4957_; lean_object* v_snd_4958_; 
v___x_4955_ = ((size_t)0ULL);
v___x_4956_ = lean_usize_of_nat(v___x_4950_);
v___x_4957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4947_, v___x_4955_, v___x_4956_, v___x_4953_);
v_snd_4958_ = lean_ctor_get(v___x_4957_, 1);
lean_inc(v_snd_4958_);
lean_dec_ref(v___x_4957_);
return v_snd_4958_;
}
}
else
{
size_t v___x_4959_; size_t v___x_4960_; lean_object* v___x_4961_; lean_object* v_snd_4962_; 
v___x_4959_ = ((size_t)0ULL);
v___x_4960_ = lean_usize_of_nat(v___x_4950_);
v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4947_, v___x_4959_, v___x_4960_, v___x_4953_);
v_snd_4962_ = lean_ctor_get(v___x_4961_, 1);
lean_inc(v_snd_4962_);
lean_dec_ref(v___x_4961_);
return v_snd_4962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4963_);
lean_dec_ref(v_sa_4963_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4965_, lean_object* v_sep_4966_, lean_object* v_sa_4967_){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4969_, lean_object* v_sep_4970_, lean_object* v_sa_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Syntax_TSepArray_getElems(v_k_4969_, v_sep_4970_, v_sa_4971_);
lean_dec_ref(v_sa_4971_);
lean_dec_ref(v_sep_4970_);
lean_dec(v_k_4969_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4973_, lean_object* v_sa_4974_, lean_object* v_e_4975_){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; 
v___x_4976_ = lean_array_get_size(v_sa_4974_);
v___x_4977_ = lean_unsigned_to_nat(0u);
v___x_4978_ = lean_nat_dec_eq(v___x_4976_, v___x_4977_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4979_ = l_Lean_mkAtom(v_sep_4973_);
v___x_4980_ = lean_array_push(v_sa_4974_, v___x_4979_);
v___x_4981_ = lean_array_push(v___x_4980_, v_e_4975_);
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec_ref(v_sa_4974_);
lean_dec_ref(v_sep_4973_);
v___x_4982_ = lean_unsigned_to_nat(1u);
v___x_4983_ = lean_mk_empty_array_with_capacity(v___x_4982_);
v___x_4984_ = lean_array_push(v___x_4983_, v_e_4975_);
return v___x_4984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4985_, lean_object* v_sep_4986_, lean_object* v_sa_4987_, lean_object* v_e_4988_){
_start:
{
lean_object* v___x_4989_; 
v___x_4989_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4986_, v_sa_4987_, v_e_4988_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4990_, lean_object* v_sep_4991_, lean_object* v_sa_4992_, lean_object* v_e_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_Syntax_TSepArray_push(v_k_4990_, v_sep_4991_, v_sa_4992_, v_e_4993_);
lean_dec(v_k_4990_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4995_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4997_);
lean_dec_ref(v_sep_4997_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4999_, lean_object* v_k_5000_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_5002_, lean_object* v_k_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_5002_, v_k_5003_);
lean_dec_ref(v_k_5003_);
lean_dec(v_sep_5002_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object* v_sep_5005_){
_start:
{
lean_object* v___x_5006_; 
v___x_5006_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___boxed), 2, 1);
lean_closure_set(v___x_5006_, 0, v_sep_5005_);
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_5007_, lean_object* v_sep_5008_){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_5009_, 0, v_k_5007_);
lean_closure_set(v___x_5009_, 1, v_sep_5008_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_5010_, lean_object* v_x_5011_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = lean_apply_1(v_inst_5010_, v_x_5011_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v___x_5015_; size_t v_sz_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
v___x_5015_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5016_ = lean_array_size(v_a_5014_);
v___x_5017_ = ((size_t)0ULL);
v___x_5018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5015_, v___f_5013_, v_sz_5016_, v___x_5017_, v_a_5014_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5019_){
_start:
{
lean_object* v___f_5020_; lean_object* v___f_5021_; 
v___f_5020_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5020_, 0, v_inst_5019_);
v___f_5021_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5021_, 0, v___f_5020_);
return v___f_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5022_, lean_object* v_k_x27_5023_, lean_object* v_inst_5024_){
_start:
{
lean_object* v___x_5025_; 
v___x_5025_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5026_, lean_object* v_k_x27_5027_, lean_object* v_inst_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5026_, v_k_x27_5027_, v_inst_5028_);
lean_dec(v_k_x27_5027_);
lean_dec(v_k_5026_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object* v_a_5030_){
_start:
{
lean_inc_ref(v_a_5030_);
return v_a_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object* v_a_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(v_a_5031_);
lean_dec_ref(v_a_5031_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5034_){
_start:
{
lean_object* v___f_5035_; 
v___f_5035_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0));
return v___f_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5036_);
lean_dec(v_k_5036_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5045_){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5046_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_5047_ = lean_box(2);
v___x_5048_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5049_ = lean_unsigned_to_nat(2u);
v___x_5050_ = lean_mk_empty_array_with_capacity(v___x_5049_);
v___x_5051_ = lean_array_push(v___x_5050_, v_id_5045_);
v___x_5052_ = lean_array_push(v___x_5051_, v___x_5048_);
v___x_5053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5047_);
lean_ctor_set(v___x_5053_, 1, v___x_5046_);
lean_ctor_set(v___x_5053_, 2, v___x_5052_);
return v___x_5053_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = 123;
v___x_5058_ = lean_box_uint32(v___x_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5059_, lean_object* v_i_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Syntax_decodeQuotedChar(v_s_5059_, v_i_5060_);
if (lean_obj_tag(v___x_5061_) == 0)
{
uint32_t v_c_5062_; uint32_t v___x_5063_; uint8_t v___x_5064_; 
v_c_5062_ = lean_string_utf8_get(v_s_5059_, v_i_5060_);
v___x_5063_ = 123;
v___x_5064_ = lean_uint32_dec_eq(v_c_5062_, v___x_5063_);
if (v___x_5064_ == 0)
{
return v___x_5061_;
}
else
{
lean_object* v_i_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v_i_5065_ = lean_string_utf8_next(v_s_5059_, v_i_5060_);
v___x_5066_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
lean_ctor_set(v___x_5067_, 1, v_i_5065_);
v___x_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
return v___x_5068_;
}
}
else
{
return v___x_5061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5069_, lean_object* v_i_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5069_, v_i_5070_);
lean_dec(v_i_5070_);
lean_dec_ref(v_s_5069_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5072_, lean_object* v_i_5073_, lean_object* v_acc_5074_){
_start:
{
uint32_t v_c_5075_; lean_object* v_i_5076_; uint8_t v___y_5078_; uint32_t v___x_5097_; uint8_t v___x_5098_; 
v_c_5075_ = lean_string_utf8_get(v_s_5072_, v_i_5073_);
v_i_5076_ = lean_string_utf8_next(v_s_5072_, v_i_5073_);
lean_dec(v_i_5073_);
v___x_5097_ = 34;
v___x_5098_ = lean_uint32_dec_eq(v_c_5075_, v___x_5097_);
if (v___x_5098_ == 0)
{
uint32_t v___x_5099_; uint8_t v___x_5100_; 
v___x_5099_ = 123;
v___x_5100_ = lean_uint32_dec_eq(v_c_5075_, v___x_5099_);
v___y_5078_ = v___x_5100_;
goto v___jp_5077_;
}
else
{
v___y_5078_ = v___x_5098_;
goto v___jp_5077_;
}
v___jp_5077_:
{
if (v___y_5078_ == 0)
{
uint8_t v___x_5079_; 
v___x_5079_ = lean_string_utf8_at_end(v_s_5072_, v_i_5076_);
if (v___x_5079_ == 0)
{
uint32_t v___x_5080_; uint8_t v___x_5081_; 
v___x_5080_ = 92;
v___x_5081_ = lean_uint32_dec_eq(v_c_5075_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; 
v___x_5082_ = lean_string_push(v_acc_5074_, v_c_5075_);
v_i_5073_ = v_i_5076_;
v_acc_5074_ = v___x_5082_;
goto _start;
}
else
{
lean_object* v___x_5084_; 
v___x_5084_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5072_, v_i_5076_);
if (lean_obj_tag(v___x_5084_) == 1)
{
lean_object* v_val_5085_; lean_object* v_fst_5086_; lean_object* v_snd_5087_; uint32_t v___x_5088_; lean_object* v___x_5089_; 
lean_dec(v_i_5076_);
v_val_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_val_5085_);
lean_dec_ref(v___x_5084_);
v_fst_5086_ = lean_ctor_get(v_val_5085_, 0);
lean_inc(v_fst_5086_);
v_snd_5087_ = lean_ctor_get(v_val_5085_, 1);
lean_inc(v_snd_5087_);
lean_dec(v_val_5085_);
v___x_5088_ = lean_unbox_uint32(v_fst_5086_);
lean_dec(v_fst_5086_);
v___x_5089_ = lean_string_push(v_acc_5074_, v___x_5088_);
v_i_5073_ = v_snd_5087_;
v_acc_5074_ = v___x_5089_;
goto _start;
}
else
{
lean_object* v___x_5091_; 
lean_dec(v___x_5084_);
lean_inc_ref(v_s_5072_);
v___x_5091_ = l_Lean_Syntax_decodeStringGap(v_s_5072_, v_i_5076_);
lean_dec(v_i_5076_);
if (lean_obj_tag(v___x_5091_) == 1)
{
lean_object* v_val_5092_; 
v_val_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_val_5092_);
lean_dec_ref(v___x_5091_);
v_i_5073_ = v_val_5092_;
goto _start;
}
else
{
lean_object* v___x_5094_; 
lean_dec(v___x_5091_);
lean_dec_ref(v_acc_5074_);
lean_dec_ref(v_s_5072_);
v___x_5094_ = lean_box(0);
return v___x_5094_;
}
}
}
}
else
{
lean_object* v___x_5095_; 
lean_dec(v_i_5076_);
lean_dec_ref(v_acc_5074_);
lean_dec_ref(v_s_5072_);
v___x_5095_ = lean_box(0);
return v___x_5095_;
}
}
else
{
lean_object* v___x_5096_; 
lean_dec(v_i_5076_);
lean_dec_ref(v_s_5072_);
v___x_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5096_, 0, v_acc_5074_);
return v___x_5096_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5101_){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5102_ = lean_unsigned_to_nat(1u);
v___x_5103_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5104_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5101_, v___x_5102_, v___x_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5108_){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5110_ = l_Lean_Syntax_isLit_x3f(v___x_5109_, v_stx_5108_);
if (lean_obj_tag(v___x_5110_) == 0)
{
return v___x_5110_;
}
else
{
lean_object* v_val_5111_; lean_object* v___x_5112_; 
v_val_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_val_5111_);
lean_dec_ref(v___x_5110_);
v___x_5112_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5111_);
return v___x_5112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5113_);
lean_dec(v_stx_5113_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5115_){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5116_ = l_Lean_Syntax_getArgs(v_stx_5115_);
v___x_5117_ = lean_unsigned_to_nat(0u);
v___x_5118_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5119_ = lean_array_get_size(v___x_5116_);
v___x_5120_ = lean_nat_dec_lt(v___x_5117_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_dec_ref(v___x_5116_);
return v___x_5118_;
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; 
v___x_5121_ = lean_box(v___x_5120_);
v___x_5122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5121_);
lean_ctor_set(v___x_5122_, 1, v___x_5118_);
v___x_5123_ = lean_nat_dec_le(v___x_5119_, v___x_5119_);
if (v___x_5123_ == 0)
{
if (v___x_5120_ == 0)
{
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5116_);
return v___x_5118_;
}
else
{
size_t v___x_5124_; size_t v___x_5125_; lean_object* v___x_5126_; lean_object* v_snd_5127_; 
v___x_5124_ = ((size_t)0ULL);
v___x_5125_ = lean_usize_of_nat(v___x_5119_);
v___x_5126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5116_, v___x_5124_, v___x_5125_, v___x_5122_);
lean_dec_ref(v___x_5116_);
v_snd_5127_ = lean_ctor_get(v___x_5126_, 1);
lean_inc(v_snd_5127_);
lean_dec_ref(v___x_5126_);
return v_snd_5127_;
}
}
else
{
size_t v___x_5128_; size_t v___x_5129_; lean_object* v___x_5130_; lean_object* v_snd_5131_; 
v___x_5128_ = ((size_t)0ULL);
v___x_5129_ = lean_usize_of_nat(v___x_5119_);
v___x_5130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5116_, v___x_5128_, v___x_5129_, v___x_5122_);
lean_dec_ref(v___x_5116_);
v_snd_5131_ = lean_ctor_get(v___x_5130_, 1);
lean_inc(v_snd_5131_);
lean_dec_ref(v___x_5130_);
return v_snd_5131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_Syntax_getSepArgs(v_stx_5132_);
lean_dec(v_stx_5132_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5134_, lean_object* v_mkElem_5135_, lean_object* v_mkLit_5136_, lean_object* v_as_5137_, size_t v_sz_5138_, size_t v_i_5139_, lean_object* v_b_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v_a_5144_; lean_object* v_a_5145_; lean_object* v_elem_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; uint8_t v___x_5157_; 
v___x_5157_ = lean_usize_dec_lt(v_i_5139_, v_sz_5138_);
if (v___x_5157_ == 0)
{
lean_object* v___x_5158_; 
lean_dec_ref(v_mkLit_5136_);
lean_dec_ref(v_mkElem_5135_);
lean_dec_ref(v_mkAppend_5134_);
v___x_5158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5158_, 0, v_b_5140_);
lean_ctor_set(v___x_5158_, 1, v___y_5142_);
return v___x_5158_;
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5160_; 
v_a_5159_ = lean_array_uget_borrowed(v_as_5137_, v_i_5139_);
v___x_5160_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5159_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v_methods_5161_; lean_object* v_quotContext_5162_; lean_object* v_currMacroScope_5163_; lean_object* v_currRecDepth_5164_; lean_object* v_maxRecDepth_5165_; lean_object* v_ref_5166_; lean_object* v_ref_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v_methods_5161_ = lean_ctor_get(v___y_5141_, 0);
v_quotContext_5162_ = lean_ctor_get(v___y_5141_, 1);
v_currMacroScope_5163_ = lean_ctor_get(v___y_5141_, 2);
v_currRecDepth_5164_ = lean_ctor_get(v___y_5141_, 3);
v_maxRecDepth_5165_ = lean_ctor_get(v___y_5141_, 4);
v_ref_5166_ = lean_ctor_get(v___y_5141_, 5);
v_ref_5167_ = l_Lean_replaceRef(v_a_5159_, v_ref_5166_);
lean_inc(v_maxRecDepth_5165_);
lean_inc(v_currRecDepth_5164_);
lean_inc(v_currMacroScope_5163_);
lean_inc(v_quotContext_5162_);
lean_inc(v_methods_5161_);
v___x_5168_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5168_, 0, v_methods_5161_);
lean_ctor_set(v___x_5168_, 1, v_quotContext_5162_);
lean_ctor_set(v___x_5168_, 2, v_currMacroScope_5163_);
lean_ctor_set(v___x_5168_, 3, v_currRecDepth_5164_);
lean_ctor_set(v___x_5168_, 4, v_maxRecDepth_5165_);
lean_ctor_set(v___x_5168_, 5, v_ref_5167_);
lean_inc_ref(v_mkElem_5135_);
lean_inc(v_a_5159_);
v___x_5169_ = lean_apply_3(v_mkElem_5135_, v_a_5159_, v___x_5168_, v___y_5142_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; lean_object* v_a_5171_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
v_a_5171_ = lean_ctor_get(v___x_5169_, 1);
lean_inc(v_a_5171_);
lean_dec_ref(v___x_5169_);
v_elem_5150_ = v_a_5170_;
v___y_5151_ = v___y_5141_;
v___y_5152_ = v_a_5171_;
goto v___jp_5149_;
}
else
{
lean_dec(v_b_5140_);
lean_dec_ref(v_mkLit_5136_);
lean_dec_ref(v_mkElem_5135_);
lean_dec_ref(v_mkAppend_5134_);
return v___x_5169_;
}
}
else
{
lean_object* v_val_5172_; uint8_t v___x_5173_; 
v_val_5172_ = lean_ctor_get(v___x_5160_, 0);
lean_inc(v_val_5172_);
lean_dec_ref(v___x_5160_);
lean_inc(v_val_5172_);
v___x_5173_ = lean_string_isempty(v_val_5172_);
if (v___x_5173_ == 0)
{
lean_object* v_methods_5174_; lean_object* v_quotContext_5175_; lean_object* v_currMacroScope_5176_; lean_object* v_currRecDepth_5177_; lean_object* v_maxRecDepth_5178_; lean_object* v_ref_5179_; lean_object* v_ref_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
v_methods_5174_ = lean_ctor_get(v___y_5141_, 0);
v_quotContext_5175_ = lean_ctor_get(v___y_5141_, 1);
v_currMacroScope_5176_ = lean_ctor_get(v___y_5141_, 2);
v_currRecDepth_5177_ = lean_ctor_get(v___y_5141_, 3);
v_maxRecDepth_5178_ = lean_ctor_get(v___y_5141_, 4);
v_ref_5179_ = lean_ctor_get(v___y_5141_, 5);
v_ref_5180_ = l_Lean_replaceRef(v_a_5159_, v_ref_5179_);
lean_inc(v_maxRecDepth_5178_);
lean_inc(v_currRecDepth_5177_);
lean_inc(v_currMacroScope_5176_);
lean_inc(v_quotContext_5175_);
lean_inc(v_methods_5174_);
v___x_5181_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5181_, 0, v_methods_5174_);
lean_ctor_set(v___x_5181_, 1, v_quotContext_5175_);
lean_ctor_set(v___x_5181_, 2, v_currMacroScope_5176_);
lean_ctor_set(v___x_5181_, 3, v_currRecDepth_5177_);
lean_ctor_set(v___x_5181_, 4, v_maxRecDepth_5178_);
lean_ctor_set(v___x_5181_, 5, v_ref_5180_);
lean_inc_ref(v_mkLit_5136_);
v___x_5182_ = lean_apply_3(v_mkLit_5136_, v_val_5172_, v___x_5181_, v___y_5142_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v_a_5184_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
v_a_5184_ = lean_ctor_get(v___x_5182_, 1);
lean_inc(v_a_5184_);
lean_dec_ref(v___x_5182_);
v_elem_5150_ = v_a_5183_;
v___y_5151_ = v___y_5141_;
v___y_5152_ = v_a_5184_;
goto v___jp_5149_;
}
else
{
lean_dec(v_b_5140_);
lean_dec_ref(v_mkLit_5136_);
lean_dec_ref(v_mkElem_5135_);
lean_dec_ref(v_mkAppend_5134_);
return v___x_5182_;
}
}
else
{
lean_dec(v_val_5172_);
v_a_5144_ = v_b_5140_;
v_a_5145_ = v___y_5142_;
goto v___jp_5143_;
}
}
}
v___jp_5143_:
{
size_t v___x_5146_; size_t v___x_5147_; 
v___x_5146_ = ((size_t)1ULL);
v___x_5147_ = lean_usize_add(v_i_5139_, v___x_5146_);
v_i_5139_ = v___x_5147_;
v_b_5140_ = v_a_5144_;
v___y_5142_ = v_a_5145_;
goto _start;
}
v___jp_5149_:
{
uint8_t v___x_5153_; 
v___x_5153_ = l_Lean_Syntax_isMissing(v_b_5140_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; 
lean_inc_ref(v_mkAppend_5134_);
lean_inc_ref(v___y_5151_);
v___x_5154_ = lean_apply_4(v_mkAppend_5134_, v_b_5140_, v_elem_5150_, v___y_5151_, v___y_5152_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v_a_5156_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
v_a_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc(v_a_5156_);
lean_dec_ref(v___x_5154_);
v_a_5144_ = v_a_5155_;
v_a_5145_ = v_a_5156_;
goto v___jp_5143_;
}
else
{
lean_dec_ref(v_mkLit_5136_);
lean_dec_ref(v_mkElem_5135_);
lean_dec_ref(v_mkAppend_5134_);
return v___x_5154_;
}
}
else
{
lean_dec(v_b_5140_);
v_a_5144_ = v_elem_5150_;
v_a_5145_ = v___y_5152_;
goto v___jp_5143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5185_, lean_object* v_mkElem_5186_, lean_object* v_mkLit_5187_, lean_object* v_as_5188_, lean_object* v_sz_5189_, lean_object* v_i_5190_, lean_object* v_b_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
size_t v_sz_boxed_5194_; size_t v_i_boxed_5195_; lean_object* v_res_5196_; 
v_sz_boxed_5194_ = lean_unbox_usize(v_sz_5189_);
lean_dec(v_sz_5189_);
v_i_boxed_5195_ = lean_unbox_usize(v_i_5190_);
lean_dec(v_i_5190_);
v_res_5196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5185_, v_mkElem_5186_, v_mkLit_5187_, v_as_5188_, v_sz_boxed_5194_, v_i_boxed_5195_, v_b_5191_, v___y_5192_, v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec_ref(v_as_5188_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5197_, lean_object* v_mkAppend_5198_, lean_object* v_mkElem_5199_, lean_object* v_mkLit_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v_result_5203_; size_t v_sz_5204_; size_t v___x_5205_; lean_object* v___x_5206_; 
v_result_5203_ = lean_box(0);
v_sz_5204_ = lean_array_size(v_chunks_5197_);
v___x_5205_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5200_);
v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5198_, v_mkElem_5199_, v_mkLit_5200_, v_chunks_5197_, v_sz_5204_, v___x_5205_, v_result_5203_, v_a_5201_, v_a_5202_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; lean_object* v_a_5208_; uint8_t v___x_5209_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc(v_a_5207_);
v_a_5208_ = lean_ctor_get(v___x_5206_, 1);
lean_inc(v_a_5208_);
v___x_5209_ = l_Lean_Syntax_isMissing(v_a_5207_);
lean_dec(v_a_5207_);
if (v___x_5209_ == 0)
{
lean_dec(v_a_5208_);
lean_dec_ref(v_mkLit_5200_);
return v___x_5206_;
}
else
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
lean_dec_ref(v___x_5206_);
v___x_5210_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5201_);
v___x_5211_ = lean_apply_3(v_mkLit_5200_, v___x_5210_, v_a_5201_, v_a_5208_);
return v___x_5211_;
}
}
else
{
lean_dec_ref(v_mkLit_5200_);
return v___x_5206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5212_, lean_object* v_mkAppend_5213_, lean_object* v_mkElem_5214_, lean_object* v_mkLit_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5212_, v_mkAppend_5213_, v_mkElem_5214_, v_mkLit_5215_, v_a_5216_, v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec_ref(v_chunks_5212_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5223_, lean_object* v_b_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v_ref_5227_; uint8_t v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v_ref_5227_ = lean_ctor_get(v___y_5225_, 5);
v___x_5228_ = 0;
v___x_5229_ = l_Lean_SourceInfo_fromRef(v_ref_5227_, v___x_5228_);
v___x_5230_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5231_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5229_);
v___x_5232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5229_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = l_Lean_Syntax_node3(v___x_5229_, v___x_5230_, v_a_5223_, v___x_5232_, v_b_5224_);
v___x_5234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5233_);
lean_ctor_set(v___x_5234_, 1, v___y_5226_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5235_, lean_object* v_b_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5235_, v_b_5236_, v___y_5237_, v___y_5238_);
lean_dec_ref(v___y_5237_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5240_, lean_object* v_a_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v_ref_5244_; uint8_t v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v_ref_5244_ = lean_ctor_get(v___y_5242_, 5);
v___x_5245_ = 0;
v___x_5246_ = l_Lean_SourceInfo_fromRef(v_ref_5244_, v___x_5245_);
v___x_5247_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5248_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5246_);
v___x_5249_ = l_Lean_Syntax_node1(v___x_5246_, v___x_5248_, v_a_5241_);
v___x_5250_ = l_Lean_Syntax_node2(v___x_5246_, v___x_5247_, v_ofInterpFn_5240_, v___x_5249_);
v___x_5251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5250_);
lean_ctor_set(v___x_5251_, 1, v___y_5243_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5252_, lean_object* v_a_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5252_, v_a_5253_, v___y_5254_, v___y_5255_);
lean_dec_ref(v___y_5254_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5257_, lean_object* v_s_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v_ref_5261_; uint8_t v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v_ref_5261_ = lean_ctor_get(v___y_5259_, 5);
v___x_5262_ = 0;
v___x_5263_ = l_Lean_SourceInfo_fromRef(v_ref_5261_, v___x_5262_);
v___x_5264_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5265_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5266_ = lean_box(2);
v___x_5267_ = l_Lean_Syntax_mkStrLit(v_s_5258_, v___x_5266_);
lean_inc(v___x_5263_);
v___x_5268_ = l_Lean_Syntax_node1(v___x_5263_, v___x_5265_, v___x_5267_);
v___x_5269_ = l_Lean_Syntax_node2(v___x_5263_, v___x_5264_, v_ofLitFn_5257_, v___x_5268_);
v___x_5270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5270_, 0, v___x_5269_);
lean_ctor_set(v___x_5270_, 1, v___y_5260_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5271_, lean_object* v_s_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v_res_5275_; 
v_res_5275_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5271_, v_s_5272_, v___y_5273_, v___y_5274_);
lean_dec_ref(v___y_5273_);
return v_res_5275_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5293_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5294_ = l_String_toRawSubstring_x27(v___x_5293_);
return v___x_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5315_, lean_object* v_type_5316_, lean_object* v_ofInterpFn_5317_, lean_object* v_ofLitFn_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
lean_object* v___f_5321_; lean_object* v___f_5322_; lean_object* v___f_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___f_5321_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5322_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5322_, 0, v_ofInterpFn_5317_);
v___f_5323_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5323_, 0, v_ofLitFn_5318_);
v___x_5324_ = l_Lean_Syntax_getArgs(v_interpStr_5315_);
v___x_5325_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5324_, v___f_5321_, v___f_5322_, v___f_5323_, v_a_5319_, v_a_5320_);
lean_dec_ref(v___x_5324_);
if (lean_obj_tag(v___x_5325_) == 0)
{
lean_object* v_a_5326_; lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5358_; 
v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
v_a_5327_ = lean_ctor_get(v___x_5325_, 1);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5329_ = v___x_5325_;
v_isShared_5330_ = v_isSharedCheck_5358_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_inc(v_a_5326_);
lean_dec(v___x_5325_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5358_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v_quotContext_5331_; lean_object* v_currMacroScope_5332_; lean_object* v_ref_5333_; uint8_t v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5356_; 
v_quotContext_5331_ = lean_ctor_get(v_a_5319_, 1);
lean_inc(v_quotContext_5331_);
v_currMacroScope_5332_ = lean_ctor_get(v_a_5319_, 2);
lean_inc(v_currMacroScope_5332_);
v_ref_5333_ = lean_ctor_get(v_a_5319_, 5);
lean_inc(v_ref_5333_);
lean_dec_ref(v_a_5319_);
v___x_5334_ = 0;
v___x_5335_ = l_Lean_SourceInfo_fromRef(v_ref_5333_, v___x_5334_);
lean_dec(v_ref_5333_);
v___x_5336_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5337_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5338_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc(v___x_5335_);
v___x_5339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5335_);
lean_ctor_set(v___x_5339_, 1, v___x_5338_);
v___x_5340_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5341_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5342_ = lean_box(0);
v___x_5343_ = l_Lean_addMacroScope(v_quotContext_5331_, v___x_5342_, v_currMacroScope_5332_);
v___x_5344_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
lean_inc(v___x_5335_);
v___x_5345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5335_);
lean_ctor_set(v___x_5345_, 1, v___x_5341_);
lean_ctor_set(v___x_5345_, 2, v___x_5343_);
lean_ctor_set(v___x_5345_, 3, v___x_5344_);
lean_inc(v___x_5335_);
v___x_5346_ = l_Lean_Syntax_node1(v___x_5335_, v___x_5340_, v___x_5345_);
lean_inc(v___x_5335_);
v___x_5347_ = l_Lean_Syntax_node2(v___x_5335_, v___x_5337_, v___x_5339_, v___x_5346_);
v___x_5348_ = ((lean_object*)(l_Lean_toolchain___closed__0));
lean_inc(v___x_5335_);
v___x_5349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5349_, 0, v___x_5335_);
lean_ctor_set(v___x_5349_, 1, v___x_5348_);
v___x_5350_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5335_);
v___x_5351_ = l_Lean_Syntax_node1(v___x_5335_, v___x_5350_, v_type_5316_);
v___x_5352_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
lean_inc(v___x_5335_);
v___x_5353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5335_);
lean_ctor_set(v___x_5353_, 1, v___x_5352_);
v___x_5354_ = l_Lean_Syntax_node5(v___x_5335_, v___x_5336_, v___x_5347_, v_a_5326_, v___x_5349_, v___x_5351_, v___x_5353_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5354_);
v___x_5356_ = v___x_5329_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5357_, 1, v_a_5327_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
else
{
lean_object* v_a_5359_; lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec_ref(v_a_5319_);
lean_dec(v_type_5316_);
v_a_5359_ = lean_ctor_get(v___x_5325_, 0);
v_a_5360_ = lean_ctor_get(v___x_5325_, 1);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5325_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_inc(v_a_5359_);
lean_dec(v___x_5325_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5359_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5368_, lean_object* v_type_5369_, lean_object* v_ofInterpFn_5370_, lean_object* v_ofLitFn_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_){
_start:
{
lean_object* v_res_5374_; 
v_res_5374_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5368_, v_type_5369_, v_ofInterpFn_5370_, v_ofLitFn_5371_, v_a_5372_, v_a_5373_);
lean_dec(v_interpStr_5368_);
return v_res_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5375_){
_start:
{
lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5376_ = lean_unsigned_to_nat(1u);
v___x_5377_ = l_Lean_Syntax_getArg(v_stx_5375_, v___x_5376_);
if (lean_obj_tag(v___x_5377_) == 2)
{
lean_object* v_val_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v_val_5378_ = lean_ctor_get(v___x_5377_, 1);
lean_inc_ref(v_val_5378_);
lean_dec_ref(v___x_5377_);
v___x_5379_ = lean_unsigned_to_nat(0u);
v___x_5380_ = lean_string_utf8_byte_size(v_val_5378_);
v___x_5381_ = lean_unsigned_to_nat(2u);
v___x_5382_ = lean_string_pos_sub(v___x_5380_, v___x_5381_);
v___x_5383_ = lean_string_utf8_extract(v_val_5378_, v___x_5379_, v___x_5382_);
lean_dec(v___x_5382_);
lean_dec_ref(v_val_5378_);
return v___x_5383_;
}
else
{
lean_object* v___x_5384_; 
lean_dec(v___x_5377_);
v___x_5384_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Lean_TSyntax_getDocString(v_stx_5385_);
lean_dec(v_stx_5385_);
return v_res_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5402_, lean_object* v_prec_5403_){
_start:
{
lean_object* v___y_5405_; lean_object* v___y_5412_; lean_object* v___y_5419_; lean_object* v___y_5426_; lean_object* v___y_5433_; 
switch(v_x_5402_)
{
case 0:
{
lean_object* v___x_5439_; uint8_t v___x_5440_; 
v___x_5439_ = lean_unsigned_to_nat(1024u);
v___x_5440_ = lean_nat_dec_le(v___x_5439_, v_prec_5403_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; 
v___x_5441_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5405_ = v___x_5441_;
goto v___jp_5404_;
}
else
{
lean_object* v___x_5442_; 
v___x_5442_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5405_ = v___x_5442_;
goto v___jp_5404_;
}
}
case 1:
{
lean_object* v___x_5443_; uint8_t v___x_5444_; 
v___x_5443_ = lean_unsigned_to_nat(1024u);
v___x_5444_ = lean_nat_dec_le(v___x_5443_, v_prec_5403_);
if (v___x_5444_ == 0)
{
lean_object* v___x_5445_; 
v___x_5445_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5412_ = v___x_5445_;
goto v___jp_5411_;
}
else
{
lean_object* v___x_5446_; 
v___x_5446_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5412_ = v___x_5446_;
goto v___jp_5411_;
}
}
case 2:
{
lean_object* v___x_5447_; uint8_t v___x_5448_; 
v___x_5447_ = lean_unsigned_to_nat(1024u);
v___x_5448_ = lean_nat_dec_le(v___x_5447_, v_prec_5403_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; 
v___x_5449_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5419_ = v___x_5449_;
goto v___jp_5418_;
}
else
{
lean_object* v___x_5450_; 
v___x_5450_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5419_ = v___x_5450_;
goto v___jp_5418_;
}
}
case 3:
{
lean_object* v___x_5451_; uint8_t v___x_5452_; 
v___x_5451_ = lean_unsigned_to_nat(1024u);
v___x_5452_ = lean_nat_dec_le(v___x_5451_, v_prec_5403_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; 
v___x_5453_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5426_ = v___x_5453_;
goto v___jp_5425_;
}
else
{
lean_object* v___x_5454_; 
v___x_5454_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5426_ = v___x_5454_;
goto v___jp_5425_;
}
}
default: 
{
lean_object* v___x_5455_; uint8_t v___x_5456_; 
v___x_5455_ = lean_unsigned_to_nat(1024u);
v___x_5456_ = lean_nat_dec_le(v___x_5455_, v_prec_5403_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5433_ = v___x_5457_;
goto v___jp_5432_;
}
else
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5433_ = v___x_5458_;
goto v___jp_5432_;
}
}
}
v___jp_5404_:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5406_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
v___x_5407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___y_5405_);
lean_ctor_set(v___x_5407_, 1, v___x_5406_);
v___x_5408_ = 0;
v___x_5409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5409_, 0, v___x_5407_);
lean_ctor_set_uint8(v___x_5409_, sizeof(void*)*1, v___x_5408_);
v___x_5410_ = l_Repr_addAppParen(v___x_5409_, v_prec_5403_);
return v___x_5410_;
}
v___jp_5411_:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; uint8_t v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5413_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
v___x_5414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5414_, 0, v___y_5412_);
lean_ctor_set(v___x_5414_, 1, v___x_5413_);
v___x_5415_ = 0;
v___x_5416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5416_, 0, v___x_5414_);
lean_ctor_set_uint8(v___x_5416_, sizeof(void*)*1, v___x_5415_);
v___x_5417_ = l_Repr_addAppParen(v___x_5416_, v_prec_5403_);
return v___x_5417_;
}
v___jp_5418_:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; uint8_t v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5420_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
v___x_5421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5421_, 0, v___y_5419_);
lean_ctor_set(v___x_5421_, 1, v___x_5420_);
v___x_5422_ = 0;
v___x_5423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5423_, 0, v___x_5421_);
lean_ctor_set_uint8(v___x_5423_, sizeof(void*)*1, v___x_5422_);
v___x_5424_ = l_Repr_addAppParen(v___x_5423_, v_prec_5403_);
return v___x_5424_;
}
v___jp_5425_:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5427_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
v___x_5428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___y_5426_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = 0;
v___x_5430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5430_, 0, v___x_5428_);
lean_ctor_set_uint8(v___x_5430_, sizeof(void*)*1, v___x_5429_);
v___x_5431_ = l_Repr_addAppParen(v___x_5430_, v_prec_5403_);
return v___x_5431_;
}
v___jp_5432_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; uint8_t v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5434_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
v___x_5435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___y_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = 0;
v___x_5437_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5437_, 0, v___x_5435_);
lean_ctor_set_uint8(v___x_5437_, sizeof(void*)*1, v___x_5436_);
v___x_5438_ = l_Repr_addAppParen(v___x_5437_, v_prec_5403_);
return v___x_5438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5459_, lean_object* v_prec_5460_){
_start:
{
uint8_t v_x_285__boxed_5461_; lean_object* v_res_5462_; 
v_x_285__boxed_5461_ = lean_unbox(v_x_5459_);
v_res_5462_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_285__boxed_5461_, v_prec_5460_);
lean_dec(v_prec_5460_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5474_, lean_object* v_prec_5475_){
_start:
{
lean_object* v___y_5477_; lean_object* v___y_5484_; lean_object* v___y_5491_; 
switch(v_x_5474_)
{
case 0:
{
lean_object* v___x_5497_; uint8_t v___x_5498_; 
v___x_5497_ = lean_unsigned_to_nat(1024u);
v___x_5498_ = lean_nat_dec_le(v___x_5497_, v_prec_5475_);
if (v___x_5498_ == 0)
{
lean_object* v___x_5499_; 
v___x_5499_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5477_ = v___x_5499_;
goto v___jp_5476_;
}
else
{
lean_object* v___x_5500_; 
v___x_5500_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5477_ = v___x_5500_;
goto v___jp_5476_;
}
}
case 1:
{
lean_object* v___x_5501_; uint8_t v___x_5502_; 
v___x_5501_ = lean_unsigned_to_nat(1024u);
v___x_5502_ = lean_nat_dec_le(v___x_5501_, v_prec_5475_);
if (v___x_5502_ == 0)
{
lean_object* v___x_5503_; 
v___x_5503_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5484_ = v___x_5503_;
goto v___jp_5483_;
}
else
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5484_ = v___x_5504_;
goto v___jp_5483_;
}
}
default: 
{
lean_object* v___x_5505_; uint8_t v___x_5506_; 
v___x_5505_ = lean_unsigned_to_nat(1024u);
v___x_5506_ = lean_nat_dec_le(v___x_5505_, v_prec_5475_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; 
v___x_5507_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5491_ = v___x_5507_;
goto v___jp_5490_;
}
else
{
lean_object* v___x_5508_; 
v___x_5508_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5491_ = v___x_5508_;
goto v___jp_5490_;
}
}
}
v___jp_5476_:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; uint8_t v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5478_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
v___x_5479_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5479_, 0, v___y_5477_);
lean_ctor_set(v___x_5479_, 1, v___x_5478_);
v___x_5480_ = 0;
v___x_5481_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5481_, 0, v___x_5479_);
lean_ctor_set_uint8(v___x_5481_, sizeof(void*)*1, v___x_5480_);
v___x_5482_ = l_Repr_addAppParen(v___x_5481_, v_prec_5475_);
return v___x_5482_;
}
v___jp_5483_:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; uint8_t v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; 
v___x_5485_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
v___x_5486_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5486_, 0, v___y_5484_);
lean_ctor_set(v___x_5486_, 1, v___x_5485_);
v___x_5487_ = 0;
v___x_5488_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5488_, 0, v___x_5486_);
lean_ctor_set_uint8(v___x_5488_, sizeof(void*)*1, v___x_5487_);
v___x_5489_ = l_Repr_addAppParen(v___x_5488_, v_prec_5475_);
return v___x_5489_;
}
v___jp_5490_:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; uint8_t v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; 
v___x_5492_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
v___x_5493_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5493_, 0, v___y_5491_);
lean_ctor_set(v___x_5493_, 1, v___x_5492_);
v___x_5494_ = 0;
v___x_5495_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5495_, 0, v___x_5493_);
lean_ctor_set_uint8(v___x_5495_, sizeof(void*)*1, v___x_5494_);
v___x_5496_ = l_Repr_addAppParen(v___x_5495_, v_prec_5475_);
return v___x_5496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5509_, lean_object* v_prec_5510_){
_start:
{
uint8_t v_x_173__boxed_5511_; lean_object* v_res_5512_; 
v_x_173__boxed_5511_ = lean_unbox(v_x_5509_);
v_res_5512_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_173__boxed_5511_, v_prec_5510_);
lean_dec(v_prec_5510_);
return v_res_5512_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; 
v___x_5524_ = lean_unsigned_to_nat(8u);
v___x_5525_ = lean_nat_to_int(v___x_5524_);
return v___x_5525_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; 
v___x_5535_ = lean_unsigned_to_nat(13u);
v___x_5536_ = lean_nat_to_int(v___x_5535_);
return v___x_5536_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5546_ = lean_unsigned_to_nat(10u);
v___x_5547_ = lean_nat_to_int(v___x_5546_);
return v___x_5547_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; 
v___x_5551_ = lean_unsigned_to_nat(14u);
v___x_5552_ = lean_nat_to_int(v___x_5551_);
return v___x_5552_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; 
v___x_5556_ = lean_unsigned_to_nat(19u);
v___x_5557_ = lean_nat_to_int(v___x_5556_);
return v___x_5557_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; 
v___x_5561_ = lean_unsigned_to_nat(20u);
v___x_5562_ = lean_nat_to_int(v___x_5561_);
return v___x_5562_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5569_ = lean_unsigned_to_nat(9u);
v___x_5570_ = lean_nat_to_int(v___x_5569_);
return v___x_5570_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = lean_unsigned_to_nat(12u);
v___x_5578_ = lean_nat_to_int(v___x_5577_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5585_){
_start:
{
uint8_t v_zeta_5586_; uint8_t v_beta_5587_; uint8_t v_eta_5588_; uint8_t v_etaStruct_5589_; uint8_t v_iota_5590_; uint8_t v_proj_5591_; uint8_t v_decide_5592_; uint8_t v_autoUnfold_5593_; uint8_t v_failIfUnchanged_5594_; uint8_t v_unfoldPartialApp_5595_; uint8_t v_zetaDelta_5596_; uint8_t v_index_5597_; uint8_t v_zetaUnused_5598_; uint8_t v_zetaHave_5599_; uint8_t v_locals_5600_; uint8_t v_instances_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; uint8_t v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v_zeta_5586_ = lean_ctor_get_uint8(v_x_5585_, 0);
v_beta_5587_ = lean_ctor_get_uint8(v_x_5585_, 1);
v_eta_5588_ = lean_ctor_get_uint8(v_x_5585_, 2);
v_etaStruct_5589_ = lean_ctor_get_uint8(v_x_5585_, 3);
v_iota_5590_ = lean_ctor_get_uint8(v_x_5585_, 4);
v_proj_5591_ = lean_ctor_get_uint8(v_x_5585_, 5);
v_decide_5592_ = lean_ctor_get_uint8(v_x_5585_, 6);
v_autoUnfold_5593_ = lean_ctor_get_uint8(v_x_5585_, 7);
v_failIfUnchanged_5594_ = lean_ctor_get_uint8(v_x_5585_, 8);
v_unfoldPartialApp_5595_ = lean_ctor_get_uint8(v_x_5585_, 9);
v_zetaDelta_5596_ = lean_ctor_get_uint8(v_x_5585_, 10);
v_index_5597_ = lean_ctor_get_uint8(v_x_5585_, 11);
v_zetaUnused_5598_ = lean_ctor_get_uint8(v_x_5585_, 12);
v_zetaHave_5599_ = lean_ctor_get_uint8(v_x_5585_, 13);
v_locals_5600_ = lean_ctor_get_uint8(v_x_5585_, 14);
v_instances_5601_ = lean_ctor_get_uint8(v_x_5585_, 15);
v___x_5602_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5603_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5604_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5605_ = lean_unsigned_to_nat(0u);
v___x_5606_ = l_Bool_repr___redArg(v_zeta_5586_);
v___x_5607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5604_);
lean_ctor_set(v___x_5607_, 1, v___x_5606_);
v___x_5608_ = 0;
v___x_5609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5609_, 0, v___x_5607_);
lean_ctor_set_uint8(v___x_5609_, sizeof(void*)*1, v___x_5608_);
v___x_5610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5603_);
lean_ctor_set(v___x_5610_, 1, v___x_5609_);
v___x_5611_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5610_);
lean_ctor_set(v___x_5612_, 1, v___x_5611_);
v___x_5613_ = lean_box(1);
v___x_5614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5614_, 0, v___x_5612_);
lean_ctor_set(v___x_5614_, 1, v___x_5613_);
v___x_5615_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5614_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5616_);
lean_ctor_set(v___x_5617_, 1, v___x_5602_);
v___x_5618_ = l_Bool_repr___redArg(v_beta_5587_);
v___x_5619_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5604_);
lean_ctor_set(v___x_5619_, 1, v___x_5618_);
v___x_5620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5620_, 0, v___x_5619_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*1, v___x_5608_);
v___x_5621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5617_);
lean_ctor_set(v___x_5621_, 1, v___x_5620_);
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
lean_ctor_set(v___x_5622_, 1, v___x_5611_);
v___x_5623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set(v___x_5623_, 1, v___x_5613_);
v___x_5624_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5623_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v___x_5602_);
v___x_5627_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5628_ = l_Bool_repr___redArg(v_eta_5588_);
v___x_5629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5627_);
lean_ctor_set(v___x_5629_, 1, v___x_5628_);
v___x_5630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5630_, 0, v___x_5629_);
lean_ctor_set_uint8(v___x_5630_, sizeof(void*)*1, v___x_5608_);
v___x_5631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5626_);
lean_ctor_set(v___x_5631_, 1, v___x_5630_);
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
lean_ctor_set(v___x_5632_, 1, v___x_5611_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v___x_5613_);
v___x_5634_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5633_);
lean_ctor_set(v___x_5635_, 1, v___x_5634_);
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5635_);
lean_ctor_set(v___x_5636_, 1, v___x_5602_);
v___x_5637_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5638_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5589_, v___x_5605_);
v___x_5639_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5637_);
lean_ctor_set(v___x_5639_, 1, v___x_5638_);
v___x_5640_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5640_, 0, v___x_5639_);
lean_ctor_set_uint8(v___x_5640_, sizeof(void*)*1, v___x_5608_);
v___x_5641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5636_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
lean_ctor_set(v___x_5642_, 1, v___x_5611_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
lean_ctor_set(v___x_5643_, 1, v___x_5613_);
v___x_5644_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5643_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
v___x_5646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5645_);
lean_ctor_set(v___x_5646_, 1, v___x_5602_);
v___x_5647_ = l_Bool_repr___redArg(v_iota_5590_);
v___x_5648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5604_);
lean_ctor_set(v___x_5648_, 1, v___x_5647_);
v___x_5649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5649_, 0, v___x_5648_);
lean_ctor_set_uint8(v___x_5649_, sizeof(void*)*1, v___x_5608_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5646_);
lean_ctor_set(v___x_5650_, 1, v___x_5649_);
v___x_5651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set(v___x_5651_, 1, v___x_5611_);
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5651_);
lean_ctor_set(v___x_5652_, 1, v___x_5613_);
v___x_5653_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5652_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5654_);
lean_ctor_set(v___x_5655_, 1, v___x_5602_);
v___x_5656_ = l_Bool_repr___redArg(v_proj_5591_);
v___x_5657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5604_);
lean_ctor_set(v___x_5657_, 1, v___x_5656_);
v___x_5658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
lean_ctor_set_uint8(v___x_5658_, sizeof(void*)*1, v___x_5608_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5655_);
lean_ctor_set(v___x_5659_, 1, v___x_5658_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set(v___x_5660_, 1, v___x_5611_);
v___x_5661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set(v___x_5661_, 1, v___x_5613_);
v___x_5662_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5661_);
lean_ctor_set(v___x_5663_, 1, v___x_5662_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5602_);
v___x_5665_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5666_ = l_Bool_repr___redArg(v_decide_5592_);
v___x_5667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5665_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set_uint8(v___x_5668_, sizeof(void*)*1, v___x_5608_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5664_);
lean_ctor_set(v___x_5669_, 1, v___x_5668_);
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5669_);
lean_ctor_set(v___x_5670_, 1, v___x_5611_);
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set(v___x_5671_, 1, v___x_5613_);
v___x_5672_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5671_);
lean_ctor_set(v___x_5673_, 1, v___x_5672_);
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5673_);
lean_ctor_set(v___x_5674_, 1, v___x_5602_);
v___x_5675_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5676_ = l_Bool_repr___redArg(v_autoUnfold_5593_);
v___x_5677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5675_);
lean_ctor_set(v___x_5677_, 1, v___x_5676_);
v___x_5678_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set_uint8(v___x_5678_, sizeof(void*)*1, v___x_5608_);
v___x_5679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5674_);
lean_ctor_set(v___x_5679_, 1, v___x_5678_);
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
lean_ctor_set(v___x_5680_, 1, v___x_5611_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5680_);
lean_ctor_set(v___x_5681_, 1, v___x_5613_);
v___x_5682_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5681_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5683_);
lean_ctor_set(v___x_5684_, 1, v___x_5602_);
v___x_5685_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5686_ = l_Bool_repr___redArg(v_failIfUnchanged_5594_);
v___x_5687_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5685_);
lean_ctor_set(v___x_5687_, 1, v___x_5686_);
v___x_5688_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set_uint8(v___x_5688_, sizeof(void*)*1, v___x_5608_);
v___x_5689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5684_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
lean_ctor_set(v___x_5690_, 1, v___x_5611_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5613_);
v___x_5692_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5691_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
lean_ctor_set(v___x_5694_, 1, v___x_5602_);
v___x_5695_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5696_ = l_Bool_repr___redArg(v_unfoldPartialApp_5595_);
v___x_5697_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5695_);
lean_ctor_set(v___x_5697_, 1, v___x_5696_);
v___x_5698_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5698_, 0, v___x_5697_);
lean_ctor_set_uint8(v___x_5698_, sizeof(void*)*1, v___x_5608_);
v___x_5699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5694_);
lean_ctor_set(v___x_5699_, 1, v___x_5698_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set(v___x_5700_, 1, v___x_5611_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
lean_ctor_set(v___x_5701_, 1, v___x_5613_);
v___x_5702_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5701_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5703_);
lean_ctor_set(v___x_5704_, 1, v___x_5602_);
v___x_5705_ = l_Bool_repr___redArg(v_zetaDelta_5596_);
v___x_5706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5637_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
v___x_5707_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
lean_ctor_set_uint8(v___x_5707_, sizeof(void*)*1, v___x_5608_);
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5704_);
lean_ctor_set(v___x_5708_, 1, v___x_5707_);
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set(v___x_5709_, 1, v___x_5611_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set(v___x_5710_, 1, v___x_5613_);
v___x_5711_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5710_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set(v___x_5713_, 1, v___x_5602_);
v___x_5714_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5715_ = l_Bool_repr___redArg(v_index_5597_);
v___x_5716_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5714_);
lean_ctor_set(v___x_5716_, 1, v___x_5715_);
v___x_5717_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
lean_ctor_set_uint8(v___x_5717_, sizeof(void*)*1, v___x_5608_);
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5713_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v___x_5611_);
v___x_5720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5719_);
lean_ctor_set(v___x_5720_, 1, v___x_5613_);
v___x_5721_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5720_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
lean_ctor_set(v___x_5723_, 1, v___x_5602_);
v___x_5724_ = l_Bool_repr___redArg(v_zetaUnused_5598_);
v___x_5725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5675_);
lean_ctor_set(v___x_5725_, 1, v___x_5724_);
v___x_5726_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5726_, 0, v___x_5725_);
lean_ctor_set_uint8(v___x_5726_, sizeof(void*)*1, v___x_5608_);
v___x_5727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5723_);
lean_ctor_set(v___x_5727_, 1, v___x_5726_);
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
lean_ctor_set(v___x_5728_, 1, v___x_5611_);
v___x_5729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set(v___x_5729_, 1, v___x_5613_);
v___x_5730_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5729_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5731_);
lean_ctor_set(v___x_5732_, 1, v___x_5602_);
v___x_5733_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5734_ = l_Bool_repr___redArg(v_zetaHave_5599_);
v___x_5735_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5733_);
lean_ctor_set(v___x_5735_, 1, v___x_5734_);
v___x_5736_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
lean_ctor_set_uint8(v___x_5736_, sizeof(void*)*1, v___x_5608_);
v___x_5737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5732_);
lean_ctor_set(v___x_5737_, 1, v___x_5736_);
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5737_);
lean_ctor_set(v___x_5738_, 1, v___x_5611_);
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
lean_ctor_set(v___x_5739_, 1, v___x_5613_);
v___x_5740_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5739_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5741_);
lean_ctor_set(v___x_5742_, 1, v___x_5602_);
v___x_5743_ = l_Bool_repr___redArg(v_locals_5600_);
v___x_5744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5665_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
v___x_5745_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5745_, 0, v___x_5744_);
lean_ctor_set_uint8(v___x_5745_, sizeof(void*)*1, v___x_5608_);
v___x_5746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5742_);
lean_ctor_set(v___x_5746_, 1, v___x_5745_);
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5746_);
lean_ctor_set(v___x_5747_, 1, v___x_5611_);
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set(v___x_5748_, 1, v___x_5613_);
v___x_5749_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5748_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
v___x_5751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
lean_ctor_set(v___x_5751_, 1, v___x_5602_);
v___x_5752_ = l_Bool_repr___redArg(v_instances_5601_);
v___x_5753_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5637_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___x_5754_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
lean_ctor_set_uint8(v___x_5754_, sizeof(void*)*1, v___x_5608_);
v___x_5755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5751_);
lean_ctor_set(v___x_5755_, 1, v___x_5754_);
v___x_5756_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5757_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
lean_ctor_set(v___x_5758_, 1, v___x_5755_);
v___x_5759_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5758_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5756_);
lean_ctor_set(v___x_5761_, 1, v___x_5760_);
v___x_5762_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5762_, 0, v___x_5761_);
lean_ctor_set_uint8(v___x_5762_, sizeof(void*)*1, v___x_5608_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5763_);
lean_dec_ref(v_x_5763_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5765_, lean_object* v_prec_5766_){
_start:
{
lean_object* v___x_5767_; 
v___x_5767_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5765_);
return v___x_5767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5768_, lean_object* v_prec_5769_){
_start:
{
lean_object* v_res_5770_; 
v_res_5770_ = l_Lean_Meta_instReprConfig_repr(v_x_5768_, v_prec_5769_);
lean_dec(v_prec_5769_);
lean_dec_ref(v_x_5768_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5778_, lean_object* v_x_5779_){
_start:
{
if (lean_obj_tag(v_x_5778_) == 0)
{
lean_object* v___x_5780_; 
v___x_5780_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5780_;
}
else
{
lean_object* v_val_5781_; lean_object* v___x_5783_; uint8_t v_isShared_5784_; uint8_t v_isSharedCheck_5792_; 
v_val_5781_ = lean_ctor_get(v_x_5778_, 0);
v_isSharedCheck_5792_ = !lean_is_exclusive(v_x_5778_);
if (v_isSharedCheck_5792_ == 0)
{
v___x_5783_ = v_x_5778_;
v_isShared_5784_ = v_isSharedCheck_5792_;
goto v_resetjp_5782_;
}
else
{
lean_inc(v_val_5781_);
lean_dec(v_x_5778_);
v___x_5783_ = lean_box(0);
v_isShared_5784_ = v_isSharedCheck_5792_;
goto v_resetjp_5782_;
}
v_resetjp_5782_:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5788_; 
v___x_5785_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5786_ = l_Nat_reprFast(v_val_5781_);
if (v_isShared_5784_ == 0)
{
lean_ctor_set_tag(v___x_5783_, 3);
lean_ctor_set(v___x_5783_, 0, v___x_5786_);
v___x_5788_ = v___x_5783_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5786_);
v___x_5788_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
lean_object* v___x_5789_; lean_object* v___x_5790_; 
v___x_5789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5789_, 0, v___x_5785_);
lean_ctor_set(v___x_5789_, 1, v___x_5788_);
v___x_5790_ = l_Repr_addAppParen(v___x_5789_, v_x_5779_);
return v___x_5790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5793_, lean_object* v_x_5794_){
_start:
{
lean_object* v_res_5795_; 
v_res_5795_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5793_, v_x_5794_);
lean_dec(v_x_5794_);
return v_res_5795_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5808_ = lean_unsigned_to_nat(21u);
v___x_5809_ = lean_nat_to_int(v___x_5808_);
return v___x_5809_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = lean_unsigned_to_nat(11u);
v___x_5817_ = lean_nat_to_int(v___x_5816_);
return v___x_5817_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = lean_unsigned_to_nat(23u);
v___x_5834_ = lean_nat_to_int(v___x_5833_);
return v___x_5834_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_unsigned_to_nat(16u);
v___x_5839_ = lean_nat_to_int(v___x_5838_);
return v___x_5839_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5846_ = lean_unsigned_to_nat(15u);
v___x_5847_ = lean_nat_to_int(v___x_5846_);
return v___x_5847_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; 
v___x_5854_ = lean_unsigned_to_nat(17u);
v___x_5855_ = lean_nat_to_int(v___x_5854_);
return v___x_5855_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5862_ = lean_unsigned_to_nat(18u);
v___x_5863_ = lean_nat_to_int(v___x_5862_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5864_){
_start:
{
lean_object* v_maxSteps_5865_; lean_object* v_maxDischargeDepth_5866_; uint8_t v_contextual_5867_; uint8_t v_memoize_5868_; uint8_t v_singlePass_5869_; uint8_t v_zeta_5870_; uint8_t v_beta_5871_; uint8_t v_eta_5872_; uint8_t v_etaStruct_5873_; uint8_t v_iota_5874_; uint8_t v_proj_5875_; uint8_t v_decide_5876_; uint8_t v_arith_5877_; uint8_t v_autoUnfold_5878_; uint8_t v_dsimp_5879_; uint8_t v_failIfUnchanged_5880_; uint8_t v_ground_5881_; uint8_t v_unfoldPartialApp_5882_; uint8_t v_zetaDelta_5883_; uint8_t v_index_5884_; uint8_t v_implicitDefEqProofs_5885_; uint8_t v_zetaUnused_5886_; uint8_t v_catchRuntime_5887_; uint8_t v_zetaHave_5888_; uint8_t v_letToHave_5889_; uint8_t v_congrConsts_5890_; uint8_t v_bitVecOfNat_5891_; uint8_t v_warnExponents_5892_; uint8_t v_suggestions_5893_; lean_object* v_maxSuggestions_5894_; uint8_t v_locals_5895_; uint8_t v_instances_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; uint8_t v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; 
v_maxSteps_5865_ = lean_ctor_get(v_x_5864_, 0);
lean_inc(v_maxSteps_5865_);
v_maxDischargeDepth_5866_ = lean_ctor_get(v_x_5864_, 1);
lean_inc(v_maxDischargeDepth_5866_);
v_contextual_5867_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3);
v_memoize_5868_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 1);
v_singlePass_5869_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 2);
v_zeta_5870_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 3);
v_beta_5871_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 4);
v_eta_5872_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 5);
v_etaStruct_5873_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 6);
v_iota_5874_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 7);
v_proj_5875_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 8);
v_decide_5876_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 9);
v_arith_5877_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 10);
v_autoUnfold_5878_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 11);
v_dsimp_5879_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5880_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 13);
v_ground_5881_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5882_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 15);
v_zetaDelta_5883_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 16);
v_index_5884_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5885_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 18);
v_zetaUnused_5886_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 19);
v_catchRuntime_5887_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 20);
v_zetaHave_5888_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 21);
v_letToHave_5889_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 22);
v_congrConsts_5890_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5891_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 24);
v_warnExponents_5892_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 25);
v_suggestions_5893_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 26);
v_maxSuggestions_5894_ = lean_ctor_get(v_x_5864_, 2);
lean_inc(v_maxSuggestions_5894_);
v_locals_5895_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 27);
v_instances_5896_ = lean_ctor_get_uint8(v_x_5864_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5864_);
v___x_5897_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5898_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5899_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5900_ = l_Nat_reprFast(v_maxSteps_5865_);
v___x_5901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5900_);
v___x_5902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5899_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = 0;
v___x_5904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5904_, 0, v___x_5902_);
lean_ctor_set_uint8(v___x_5904_, sizeof(void*)*1, v___x_5903_);
v___x_5905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5898_);
lean_ctor_set(v___x_5905_, 1, v___x_5904_);
v___x_5906_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5905_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = lean_box(1);
v___x_5909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5907_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5909_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
lean_ctor_set(v___x_5912_, 1, v___x_5897_);
v___x_5913_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5914_ = l_Nat_reprFast(v_maxDischargeDepth_5866_);
v___x_5915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5914_);
v___x_5916_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5913_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5917_, 0, v___x_5916_);
lean_ctor_set_uint8(v___x_5917_, sizeof(void*)*1, v___x_5903_);
v___x_5918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5912_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
v___x_5919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
lean_ctor_set(v___x_5919_, 1, v___x_5906_);
v___x_5920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5919_);
lean_ctor_set(v___x_5920_, 1, v___x_5908_);
v___x_5921_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5920_);
lean_ctor_set(v___x_5922_, 1, v___x_5921_);
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
lean_ctor_set(v___x_5923_, 1, v___x_5897_);
v___x_5924_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5925_ = lean_unsigned_to_nat(0u);
v___x_5926_ = l_Bool_repr___redArg(v_contextual_5867_);
v___x_5927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5924_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
v___x_5928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*1, v___x_5903_);
v___x_5929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5923_);
lean_ctor_set(v___x_5929_, 1, v___x_5928_);
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
lean_ctor_set(v___x_5930_, 1, v___x_5906_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5908_);
v___x_5932_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5931_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5897_);
v___x_5935_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5936_ = l_Bool_repr___redArg(v_memoize_5868_);
v___x_5937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5935_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
lean_ctor_set_uint8(v___x_5938_, sizeof(void*)*1, v___x_5903_);
v___x_5939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5934_);
lean_ctor_set(v___x_5939_, 1, v___x_5938_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5939_);
lean_ctor_set(v___x_5940_, 1, v___x_5906_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5908_);
v___x_5942_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5941_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
lean_ctor_set(v___x_5944_, 1, v___x_5897_);
v___x_5945_ = l_Bool_repr___redArg(v_singlePass_5869_);
v___x_5946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5924_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set_uint8(v___x_5947_, sizeof(void*)*1, v___x_5903_);
v___x_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5944_);
lean_ctor_set(v___x_5948_, 1, v___x_5947_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set(v___x_5949_, 1, v___x_5906_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set(v___x_5950_, 1, v___x_5908_);
v___x_5951_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5950_);
lean_ctor_set(v___x_5952_, 1, v___x_5951_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5952_);
lean_ctor_set(v___x_5953_, 1, v___x_5897_);
v___x_5954_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5955_ = l_Bool_repr___redArg(v_zeta_5870_);
v___x_5956_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5954_);
lean_ctor_set(v___x_5956_, 1, v___x_5955_);
v___x_5957_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
lean_ctor_set_uint8(v___x_5957_, sizeof(void*)*1, v___x_5903_);
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5953_);
lean_ctor_set(v___x_5958_, 1, v___x_5957_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
lean_ctor_set(v___x_5959_, 1, v___x_5906_);
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5959_);
lean_ctor_set(v___x_5960_, 1, v___x_5908_);
v___x_5961_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5960_);
lean_ctor_set(v___x_5962_, 1, v___x_5961_);
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
lean_ctor_set(v___x_5963_, 1, v___x_5897_);
v___x_5964_ = l_Bool_repr___redArg(v_beta_5871_);
v___x_5965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5954_);
lean_ctor_set(v___x_5965_, 1, v___x_5964_);
v___x_5966_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set_uint8(v___x_5966_, sizeof(void*)*1, v___x_5903_);
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5963_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5967_);
lean_ctor_set(v___x_5968_, 1, v___x_5906_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5908_);
v___x_5970_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5969_);
lean_ctor_set(v___x_5971_, 1, v___x_5970_);
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
lean_ctor_set(v___x_5972_, 1, v___x_5897_);
v___x_5973_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5974_ = l_Bool_repr___redArg(v_eta_5872_);
v___x_5975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5973_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set_uint8(v___x_5976_, sizeof(void*)*1, v___x_5903_);
v___x_5977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5972_);
lean_ctor_set(v___x_5977_, 1, v___x_5976_);
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5977_);
lean_ctor_set(v___x_5978_, 1, v___x_5906_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5908_);
v___x_5980_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5979_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5981_);
lean_ctor_set(v___x_5982_, 1, v___x_5897_);
v___x_5983_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5984_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5873_, v___x_5925_);
v___x_5985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5983_);
lean_ctor_set(v___x_5985_, 1, v___x_5984_);
v___x_5986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5986_, 0, v___x_5985_);
lean_ctor_set_uint8(v___x_5986_, sizeof(void*)*1, v___x_5903_);
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5982_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set(v___x_5988_, 1, v___x_5906_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5988_);
lean_ctor_set(v___x_5989_, 1, v___x_5908_);
v___x_5990_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5991_);
lean_ctor_set(v___x_5992_, 1, v___x_5897_);
v___x_5993_ = l_Bool_repr___redArg(v_iota_5874_);
v___x_5994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5954_);
lean_ctor_set(v___x_5994_, 1, v___x_5993_);
v___x_5995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5995_, 0, v___x_5994_);
lean_ctor_set_uint8(v___x_5995_, sizeof(void*)*1, v___x_5903_);
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5992_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set(v___x_5997_, 1, v___x_5906_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5997_);
lean_ctor_set(v___x_5998_, 1, v___x_5908_);
v___x_5999_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5998_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v___x_6001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set(v___x_6001_, 1, v___x_5897_);
v___x_6002_ = l_Bool_repr___redArg(v_proj_5875_);
v___x_6003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_5954_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
v___x_6004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set_uint8(v___x_6004_, sizeof(void*)*1, v___x_5903_);
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6001_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___x_5906_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5908_);
v___x_6008_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6007_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set(v___x_6010_, 1, v___x_5897_);
v___x_6011_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6012_ = l_Bool_repr___redArg(v_decide_5876_);
v___x_6013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6011_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
v___x_6014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set_uint8(v___x_6014_, sizeof(void*)*1, v___x_5903_);
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6010_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5906_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5908_);
v___x_6018_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6017_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_5897_);
v___x_6021_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6022_ = l_Bool_repr___redArg(v_arith_5877_);
v___x_6023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6021_);
lean_ctor_set(v___x_6023_, 1, v___x_6022_);
v___x_6024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set_uint8(v___x_6024_, sizeof(void*)*1, v___x_5903_);
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6020_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_5906_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_5908_);
v___x_6028_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6027_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
lean_ctor_set(v___x_6030_, 1, v___x_5897_);
v___x_6031_ = l_Bool_repr___redArg(v_autoUnfold_5878_);
v___x_6032_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_5924_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
v___x_6033_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set_uint8(v___x_6033_, sizeof(void*)*1, v___x_5903_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6030_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set(v___x_6035_, 1, v___x_5906_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
lean_ctor_set(v___x_6036_, 1, v___x_5908_);
v___x_6037_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6036_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6038_);
lean_ctor_set(v___x_6039_, 1, v___x_5897_);
v___x_6040_ = l_Bool_repr___redArg(v_dsimp_5879_);
v___x_6041_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6021_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set_uint8(v___x_6042_, sizeof(void*)*1, v___x_5903_);
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6039_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_5906_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set(v___x_6045_, 1, v___x_5908_);
v___x_6046_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6045_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set(v___x_6048_, 1, v___x_5897_);
v___x_6049_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6050_ = l_Bool_repr___redArg(v_failIfUnchanged_5880_);
v___x_6051_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6049_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6052_, 0, v___x_6051_);
lean_ctor_set_uint8(v___x_6052_, sizeof(void*)*1, v___x_5903_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6048_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5906_);
v___x_6055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_5908_);
v___x_6056_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6055_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
lean_ctor_set(v___x_6058_, 1, v___x_5897_);
v___x_6059_ = l_Bool_repr___redArg(v_ground_5881_);
v___x_6060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6011_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set_uint8(v___x_6061_, sizeof(void*)*1, v___x_5903_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6058_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5906_);
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set(v___x_6064_, 1, v___x_5908_);
v___x_6065_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6064_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v___x_5897_);
v___x_6068_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6069_ = l_Bool_repr___redArg(v_unfoldPartialApp_5882_);
v___x_6070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
lean_ctor_set_uint8(v___x_6071_, sizeof(void*)*1, v___x_5903_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6067_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_5906_);
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
lean_ctor_set(v___x_6074_, 1, v___x_5908_);
v___x_6075_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6074_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6076_);
lean_ctor_set(v___x_6077_, 1, v___x_5897_);
v___x_6078_ = l_Bool_repr___redArg(v_zetaDelta_5883_);
v___x_6079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_5983_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___x_6080_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
lean_ctor_set_uint8(v___x_6080_, sizeof(void*)*1, v___x_5903_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6077_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5906_);
v___x_6083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set(v___x_6083_, 1, v___x_5908_);
v___x_6084_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6083_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
lean_ctor_set(v___x_6086_, 1, v___x_5897_);
v___x_6087_ = l_Bool_repr___redArg(v_index_5884_);
v___x_6088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6021_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set_uint8(v___x_6089_, sizeof(void*)*1, v___x_5903_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6086_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_5906_);
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
lean_ctor_set(v___x_6092_, 1, v___x_5908_);
v___x_6093_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6092_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set(v___x_6095_, 1, v___x_5897_);
v___x_6096_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6097_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5885_);
v___x_6098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6096_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set_uint8(v___x_6099_, sizeof(void*)*1, v___x_5903_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6095_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5906_);
v___x_6102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_5908_);
v___x_6103_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6102_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_5897_);
v___x_6106_ = l_Bool_repr___redArg(v_zetaUnused_5886_);
v___x_6107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_5924_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set_uint8(v___x_6108_, sizeof(void*)*1, v___x_5903_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6105_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_5906_);
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set(v___x_6111_, 1, v___x_5908_);
v___x_6112_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6111_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set(v___x_6114_, 1, v___x_5897_);
v___x_6115_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6116_ = l_Bool_repr___redArg(v_catchRuntime_5887_);
v___x_6117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6115_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set_uint8(v___x_6118_, sizeof(void*)*1, v___x_5903_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6114_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_5906_);
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set(v___x_6121_, 1, v___x_5908_);
v___x_6122_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6121_);
lean_ctor_set(v___x_6123_, 1, v___x_6122_);
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set(v___x_6124_, 1, v___x_5897_);
v___x_6125_ = l_Bool_repr___redArg(v_zetaHave_5888_);
v___x_6126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_5899_);
lean_ctor_set(v___x_6126_, 1, v___x_6125_);
v___x_6127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
lean_ctor_set_uint8(v___x_6127_, sizeof(void*)*1, v___x_5903_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6124_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_5906_);
v___x_6130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
lean_ctor_set(v___x_6130_, 1, v___x_5908_);
v___x_6131_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6130_);
lean_ctor_set(v___x_6132_, 1, v___x_6131_);
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set(v___x_6133_, 1, v___x_5897_);
v___x_6134_ = l_Bool_repr___redArg(v_letToHave_5889_);
v___x_6135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_5983_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
v___x_6136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set_uint8(v___x_6136_, sizeof(void*)*1, v___x_5903_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6133_);
lean_ctor_set(v___x_6137_, 1, v___x_6136_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_5906_);
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set(v___x_6139_, 1, v___x_5908_);
v___x_6140_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6139_);
lean_ctor_set(v___x_6141_, 1, v___x_6140_);
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6141_);
lean_ctor_set(v___x_6142_, 1, v___x_5897_);
v___x_6143_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6144_ = l_Bool_repr___redArg(v_congrConsts_5890_);
v___x_6145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6143_);
lean_ctor_set(v___x_6145_, 1, v___x_6144_);
v___x_6146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*1, v___x_5903_);
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6142_);
lean_ctor_set(v___x_6147_, 1, v___x_6146_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_5906_);
v___x_6149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set(v___x_6149_, 1, v___x_5908_);
v___x_6150_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6149_);
lean_ctor_set(v___x_6151_, 1, v___x_6150_);
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
lean_ctor_set(v___x_6152_, 1, v___x_5897_);
v___x_6153_ = l_Bool_repr___redArg(v_bitVecOfNat_5891_);
v___x_6154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6143_);
lean_ctor_set(v___x_6154_, 1, v___x_6153_);
v___x_6155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set_uint8(v___x_6155_, sizeof(void*)*1, v___x_5903_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6152_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set(v___x_6157_, 1, v___x_5906_);
v___x_6158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
lean_ctor_set(v___x_6158_, 1, v___x_5908_);
v___x_6159_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6158_);
lean_ctor_set(v___x_6160_, 1, v___x_6159_);
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
lean_ctor_set(v___x_6161_, 1, v___x_5897_);
v___x_6162_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6163_ = l_Bool_repr___redArg(v_warnExponents_5892_);
v___x_6164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6162_);
lean_ctor_set(v___x_6164_, 1, v___x_6163_);
v___x_6165_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6165_, 0, v___x_6164_);
lean_ctor_set_uint8(v___x_6165_, sizeof(void*)*1, v___x_5903_);
v___x_6166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6161_);
lean_ctor_set(v___x_6166_, 1, v___x_6165_);
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6166_);
lean_ctor_set(v___x_6167_, 1, v___x_5906_);
v___x_6168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6167_);
lean_ctor_set(v___x_6168_, 1, v___x_5908_);
v___x_6169_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6168_);
lean_ctor_set(v___x_6170_, 1, v___x_6169_);
v___x_6171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
lean_ctor_set(v___x_6171_, 1, v___x_5897_);
v___x_6172_ = l_Bool_repr___redArg(v_suggestions_5893_);
v___x_6173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6143_);
lean_ctor_set(v___x_6173_, 1, v___x_6172_);
v___x_6174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6174_, 0, v___x_6173_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*1, v___x_5903_);
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6171_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set(v___x_6176_, 1, v___x_5906_);
v___x_6177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set(v___x_6177_, 1, v___x_5908_);
v___x_6178_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6177_);
lean_ctor_set(v___x_6179_, 1, v___x_6178_);
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6179_);
lean_ctor_set(v___x_6180_, 1, v___x_5897_);
v___x_6181_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6182_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5894_, v___x_5925_);
v___x_6183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6181_);
lean_ctor_set(v___x_6183_, 1, v___x_6182_);
v___x_6184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6184_, 0, v___x_6183_);
lean_ctor_set_uint8(v___x_6184_, sizeof(void*)*1, v___x_5903_);
v___x_6185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6180_);
lean_ctor_set(v___x_6185_, 1, v___x_6184_);
v___x_6186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6185_);
lean_ctor_set(v___x_6186_, 1, v___x_5906_);
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___x_5908_);
v___x_6188_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6187_);
lean_ctor_set(v___x_6189_, 1, v___x_6188_);
v___x_6190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6189_);
lean_ctor_set(v___x_6190_, 1, v___x_5897_);
v___x_6191_ = l_Bool_repr___redArg(v_locals_5895_);
v___x_6192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6011_);
lean_ctor_set(v___x_6192_, 1, v___x_6191_);
v___x_6193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6193_, 0, v___x_6192_);
lean_ctor_set_uint8(v___x_6193_, sizeof(void*)*1, v___x_5903_);
v___x_6194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6190_);
lean_ctor_set(v___x_6194_, 1, v___x_6193_);
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6194_);
lean_ctor_set(v___x_6195_, 1, v___x_5906_);
v___x_6196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
lean_ctor_set(v___x_6196_, 1, v___x_5908_);
v___x_6197_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6196_);
lean_ctor_set(v___x_6198_, 1, v___x_6197_);
v___x_6199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6198_);
lean_ctor_set(v___x_6199_, 1, v___x_5897_);
v___x_6200_ = l_Bool_repr___redArg(v_instances_5896_);
v___x_6201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_5983_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
lean_ctor_set_uint8(v___x_6202_, sizeof(void*)*1, v___x_5903_);
v___x_6203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6199_);
lean_ctor_set(v___x_6203_, 1, v___x_6202_);
v___x_6204_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6205_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6205_);
lean_ctor_set(v___x_6206_, 1, v___x_6203_);
v___x_6207_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6206_);
lean_ctor_set(v___x_6208_, 1, v___x_6207_);
v___x_6209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6204_);
lean_ctor_set(v___x_6209_, 1, v___x_6208_);
v___x_6210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6210_, 0, v___x_6209_);
lean_ctor_set_uint8(v___x_6210_, sizeof(void*)*1, v___x_5903_);
return v___x_6210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6211_, lean_object* v_prec_6212_){
_start:
{
lean_object* v___x_6213_; 
v___x_6213_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6211_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6214_, lean_object* v_prec_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6214_, v_prec_6215_);
lean_dec(v_prec_6215_);
return v_res_6216_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6219_, lean_object* v_x_6220_){
_start:
{
if (lean_obj_tag(v_x_6220_) == 0)
{
uint8_t v___x_6221_; 
v___x_6221_ = 0;
return v___x_6221_;
}
else
{
lean_object* v_head_6222_; lean_object* v_tail_6223_; uint8_t v___x_6224_; 
v_head_6222_ = lean_ctor_get(v_x_6220_, 0);
v_tail_6223_ = lean_ctor_get(v_x_6220_, 1);
v___x_6224_ = lean_nat_dec_eq(v_a_6219_, v_head_6222_);
if (v___x_6224_ == 0)
{
v_x_6220_ = v_tail_6223_;
goto _start;
}
else
{
return v___x_6224_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6226_, lean_object* v_x_6227_){
_start:
{
uint8_t v_res_6228_; lean_object* v_r_6229_; 
v_res_6228_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6226_, v_x_6227_);
lean_dec(v_x_6227_);
lean_dec(v_a_6226_);
v_r_6229_ = lean_box(v_res_6228_);
return v_r_6229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6230_, lean_object* v_x_6231_){
_start:
{
switch(lean_obj_tag(v_x_6230_))
{
case 0:
{
uint8_t v___x_6232_; 
v___x_6232_ = 1;
return v___x_6232_;
}
case 1:
{
lean_object* v_idxs_6233_; uint8_t v___x_6234_; 
v_idxs_6233_ = lean_ctor_get(v_x_6230_, 0);
v___x_6234_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6231_, v_idxs_6233_);
return v___x_6234_;
}
default: 
{
lean_object* v_idxs_6235_; uint8_t v___x_6236_; 
v_idxs_6235_ = lean_ctor_get(v_x_6230_, 0);
v___x_6236_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6231_, v_idxs_6235_);
if (v___x_6236_ == 0)
{
uint8_t v___x_6237_; 
v___x_6237_ = 1;
return v___x_6237_;
}
else
{
uint8_t v___x_6238_; 
v___x_6238_ = 0;
return v___x_6238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6239_, lean_object* v_x_6240_){
_start:
{
uint8_t v_res_6241_; lean_object* v_r_6242_; 
v_res_6241_ = l_Lean_Meta_Occurrences_contains(v_x_6239_, v_x_6240_);
lean_dec(v_x_6240_);
lean_dec(v_x_6239_);
v_r_6242_ = lean_box(v_res_6241_);
return v_r_6242_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6243_){
_start:
{
if (lean_obj_tag(v_x_6243_) == 0)
{
uint8_t v___x_6244_; 
v___x_6244_ = 1;
return v___x_6244_;
}
else
{
uint8_t v___x_6245_; 
v___x_6245_ = 0;
return v___x_6245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6246_){
_start:
{
uint8_t v_res_6247_; lean_object* v_r_6248_; 
v_res_6247_ = l_Lean_Meta_Occurrences_isAll(v_x_6246_);
lean_dec(v_x_6246_);
v_r_6248_ = lean_box(v_res_6247_);
return v_r_6248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6249_){
_start:
{
switch(v_x_6249_)
{
case 0:
{
lean_object* v___x_6250_; 
v___x_6250_ = lean_unsigned_to_nat(0u);
return v___x_6250_;
}
case 1:
{
lean_object* v___x_6251_; 
v___x_6251_ = lean_unsigned_to_nat(1u);
return v___x_6251_;
}
default: 
{
lean_object* v___x_6252_; 
v___x_6252_ = lean_unsigned_to_nat(2u);
return v___x_6252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6253_){
_start:
{
uint8_t v_x_boxed_6254_; lean_object* v_res_6255_; 
v_x_boxed_6254_ = lean_unbox(v_x_6253_);
v_res_6255_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6254_);
return v_res_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t v_x_6256_){
_start:
{
lean_object* v___x_6257_; 
v___x_6257_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_6256_);
return v___x_6257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object* v_x_6258_){
_start:
{
uint8_t v_x_4__boxed_6259_; lean_object* v_res_6260_; 
v_x_4__boxed_6259_ = lean_unbox(v_x_6258_);
v_res_6260_ = l_Lean_Meta_ApplyNewGoals_toCtorIdx(v_x_4__boxed_6259_);
return v_res_6260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6261_){
_start:
{
lean_inc(v_k_6261_);
return v_k_6261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6262_){
_start:
{
lean_object* v_res_6263_; 
v_res_6263_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6262_);
lean_dec(v_k_6262_);
return v_res_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6264_, lean_object* v_ctorIdx_6265_, uint8_t v_t_6266_, lean_object* v_h_6267_, lean_object* v_k_6268_){
_start:
{
lean_inc(v_k_6268_);
return v_k_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6269_, lean_object* v_ctorIdx_6270_, lean_object* v_t_6271_, lean_object* v_h_6272_, lean_object* v_k_6273_){
_start:
{
uint8_t v_t_boxed_6274_; lean_object* v_res_6275_; 
v_t_boxed_6274_ = lean_unbox(v_t_6271_);
v_res_6275_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6269_, v_ctorIdx_6270_, v_t_boxed_6274_, v_h_6272_, v_k_6273_);
lean_dec(v_k_6273_);
lean_dec(v_ctorIdx_6270_);
return v_res_6275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6276_){
_start:
{
lean_inc(v_nonDependentFirst_6276_);
return v_nonDependentFirst_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6277_){
_start:
{
lean_object* v_res_6278_; 
v_res_6278_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6277_);
lean_dec(v_nonDependentFirst_6277_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6279_, uint8_t v_t_6280_, lean_object* v_h_6281_, lean_object* v_nonDependentFirst_6282_){
_start:
{
lean_inc(v_nonDependentFirst_6282_);
return v_nonDependentFirst_6282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6283_, lean_object* v_t_6284_, lean_object* v_h_6285_, lean_object* v_nonDependentFirst_6286_){
_start:
{
uint8_t v_t_boxed_6287_; lean_object* v_res_6288_; 
v_t_boxed_6287_ = lean_unbox(v_t_6284_);
v_res_6288_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6283_, v_t_boxed_6287_, v_h_6285_, v_nonDependentFirst_6286_);
lean_dec(v_nonDependentFirst_6286_);
return v_res_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6289_){
_start:
{
lean_inc(v_nonDependentOnly_6289_);
return v_nonDependentOnly_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6290_){
_start:
{
lean_object* v_res_6291_; 
v_res_6291_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6290_);
lean_dec(v_nonDependentOnly_6290_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6292_, uint8_t v_t_6293_, lean_object* v_h_6294_, lean_object* v_nonDependentOnly_6295_){
_start:
{
lean_inc(v_nonDependentOnly_6295_);
return v_nonDependentOnly_6295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6296_, lean_object* v_t_6297_, lean_object* v_h_6298_, lean_object* v_nonDependentOnly_6299_){
_start:
{
uint8_t v_t_boxed_6300_; lean_object* v_res_6301_; 
v_t_boxed_6300_ = lean_unbox(v_t_6297_);
v_res_6301_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6296_, v_t_boxed_6300_, v_h_6298_, v_nonDependentOnly_6299_);
lean_dec(v_nonDependentOnly_6299_);
return v_res_6301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6302_){
_start:
{
lean_inc(v_all_6302_);
return v_all_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6303_){
_start:
{
lean_object* v_res_6304_; 
v_res_6304_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6303_);
lean_dec(v_all_6303_);
return v_res_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6305_, uint8_t v_t_6306_, lean_object* v_h_6307_, lean_object* v_all_6308_){
_start:
{
lean_inc(v_all_6308_);
return v_all_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6309_, lean_object* v_t_6310_, lean_object* v_h_6311_, lean_object* v_all_6312_){
_start:
{
uint8_t v_t_boxed_6313_; lean_object* v_res_6314_; 
v_t_boxed_6313_ = lean_unbox(v_t_6310_);
v_res_6314_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6309_, v_t_boxed_6313_, v_h_6311_, v_all_6312_);
lean_dec(v_all_6312_);
return v_res_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6328_){
_start:
{
lean_object* v___x_6329_; uint8_t v___x_6330_; 
v___x_6329_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6328_);
v___x_6330_ = l_Lean_Syntax_isOfKind(v_c_6328_, v___x_6329_);
if (v___x_6330_ == 0)
{
lean_object* v___x_6331_; uint8_t v___x_6332_; 
v___x_6331_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6328_);
v___x_6332_ = l_Lean_Syntax_isOfKind(v_c_6328_, v___x_6331_);
if (v___x_6332_ == 0)
{
lean_object* v___x_6333_; uint8_t v___x_6334_; 
v___x_6333_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6328_);
v___x_6334_ = l_Lean_Syntax_isOfKind(v_c_6328_, v___x_6333_);
if (v___x_6334_ == 0)
{
lean_object* v___x_6335_; 
lean_dec(v_c_6328_);
v___x_6335_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6335_;
}
else
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; 
v___x_6336_ = lean_unsigned_to_nat(1u);
v___x_6337_ = lean_mk_empty_array_with_capacity(v___x_6336_);
v___x_6338_ = lean_array_push(v___x_6337_, v_c_6328_);
return v___x_6338_;
}
}
else
{
lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6339_ = lean_unsigned_to_nat(0u);
v___x_6340_ = l_Lean_Syntax_getArg(v_c_6328_, v___x_6339_);
lean_dec(v_c_6328_);
v___x_6341_ = l_Lean_Syntax_getArgs(v___x_6340_);
lean_dec(v___x_6340_);
return v___x_6341_;
}
}
else
{
lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; uint8_t v___x_6346_; 
v___x_6342_ = l_Lean_Syntax_getArgs(v_c_6328_);
lean_dec(v_c_6328_);
v___x_6343_ = lean_unsigned_to_nat(0u);
v___x_6344_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6345_ = lean_array_get_size(v___x_6342_);
v___x_6346_ = lean_nat_dec_lt(v___x_6343_, v___x_6345_);
if (v___x_6346_ == 0)
{
lean_dec_ref(v___x_6342_);
return v___x_6344_;
}
else
{
uint8_t v___x_6347_; 
v___x_6347_ = lean_nat_dec_le(v___x_6345_, v___x_6345_);
if (v___x_6347_ == 0)
{
if (v___x_6346_ == 0)
{
lean_dec_ref(v___x_6342_);
return v___x_6344_;
}
else
{
size_t v___x_6348_; size_t v___x_6349_; lean_object* v___x_6350_; 
v___x_6348_ = ((size_t)0ULL);
v___x_6349_ = lean_usize_of_nat(v___x_6345_);
v___x_6350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6342_, v___x_6348_, v___x_6349_, v___x_6344_);
lean_dec_ref(v___x_6342_);
return v___x_6350_;
}
}
else
{
size_t v___x_6351_; size_t v___x_6352_; lean_object* v___x_6353_; 
v___x_6351_ = ((size_t)0ULL);
v___x_6352_ = lean_usize_of_nat(v___x_6345_);
v___x_6353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6342_, v___x_6351_, v___x_6352_, v___x_6344_);
lean_dec_ref(v___x_6342_);
return v___x_6353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6354_, size_t v_i_6355_, size_t v_stop_6356_, lean_object* v_b_6357_){
_start:
{
uint8_t v___x_6358_; 
v___x_6358_ = lean_usize_dec_eq(v_i_6355_, v_stop_6356_);
if (v___x_6358_ == 0)
{
lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; size_t v___x_6362_; size_t v___x_6363_; 
v___x_6359_ = lean_array_uget_borrowed(v_as_6354_, v_i_6355_);
lean_inc(v___x_6359_);
v___x_6360_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6359_);
v___x_6361_ = l_Array_append___redArg(v_b_6357_, v___x_6360_);
lean_dec_ref(v___x_6360_);
v___x_6362_ = ((size_t)1ULL);
v___x_6363_ = lean_usize_add(v_i_6355_, v___x_6362_);
v_i_6355_ = v___x_6363_;
v_b_6357_ = v___x_6361_;
goto _start;
}
else
{
return v_b_6357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6365_, lean_object* v_i_6366_, lean_object* v_stop_6367_, lean_object* v_b_6368_){
_start:
{
size_t v_i_boxed_6369_; size_t v_stop_boxed_6370_; lean_object* v_res_6371_; 
v_i_boxed_6369_ = lean_unbox_usize(v_i_6366_);
lean_dec(v_i_6366_);
v_stop_boxed_6370_ = lean_unbox_usize(v_stop_6367_);
lean_dec(v_stop_6367_);
v_res_6371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6365_, v_i_boxed_6369_, v_stop_boxed_6370_, v_b_6368_);
lean_dec_ref(v_as_6365_);
return v_res_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6372_){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6373_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6374_ = lean_box(2);
v___x_6375_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6376_, 0, v___x_6374_);
lean_ctor_set(v___x_6376_, 1, v___x_6375_);
lean_ctor_set(v___x_6376_, 2, v_items_6372_);
v___x_6377_ = l_Lean_Syntax_node1(v___x_6374_, v___x_6373_, v___x_6376_);
return v___x_6377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6378_, lean_object* v_cfg_x27_6379_){
_start:
{
lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6380_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6378_);
v___x_6381_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6379_);
v___x_6382_ = l_Array_append___redArg(v___x_6380_, v___x_6381_);
lean_dec_ref(v___x_6381_);
v___x_6383_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6382_);
return v___x_6383_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
