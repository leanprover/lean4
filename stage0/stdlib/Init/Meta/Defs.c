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
static const lean_closure_object l_Lean_instQuoteNameMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNameMkStr1___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_evalPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unexpected priority"};
static const lean_object* l_Lean_evalPrio___closed__0 = (const lean_object*)&l_Lean_evalPrio___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_1848__boxed_2379_; uint8_t v_res_2380_; lean_object* v_r_2381_; 
v___x_1848__boxed_2379_ = lean_unbox(v___x_2377_);
v_res_2380_ = l_Lean_expandMacros___lam__0(v___x_1848__boxed_2379_, v_k_2378_);
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
lean_object* v_methods_2393_; lean_object* v_quotContext_2394_; lean_object* v_currMacroScope_2395_; lean_object* v_currRecDepth_2396_; lean_object* v_maxRecDepth_2397_; lean_object* v_ref_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2468_; 
v_methods_2393_ = lean_ctor_get(v_a_2385_, 0);
v_quotContext_2394_ = lean_ctor_get(v_a_2385_, 1);
v_currMacroScope_2395_ = lean_ctor_get(v_a_2385_, 2);
v_currRecDepth_2396_ = lean_ctor_get(v_a_2385_, 3);
v_maxRecDepth_2397_ = lean_ctor_get(v_a_2385_, 4);
v_ref_2398_ = lean_ctor_get(v_a_2385_, 5);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_2385_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2400_ = v_a_2385_;
v_isShared_2401_ = v_isSharedCheck_2468_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_ref_2398_);
lean_inc(v_maxRecDepth_2397_);
lean_inc(v_currRecDepth_2396_);
lean_inc(v_currMacroScope_2395_);
lean_inc(v_quotContext_2394_);
lean_inc(v_methods_2393_);
lean_dec(v_a_2385_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2468_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v_ref_2402_; lean_object* v___x_2404_; 
v_ref_2402_ = l_Lean_replaceRef(v_stx_2383_, v_ref_2398_);
lean_dec(v_ref_2398_);
lean_inc(v_ref_2402_);
lean_inc(v_maxRecDepth_2397_);
lean_inc(v_currRecDepth_2396_);
lean_inc(v_currMacroScope_2395_);
lean_inc(v_quotContext_2394_);
lean_inc(v_methods_2393_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 5, v_ref_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_methods_2393_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_quotContext_2394_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_currMacroScope_2395_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_currRecDepth_2396_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_maxRecDepth_2397_);
lean_ctor_set(v_reuseFailAlloc_2467_, 5, v_ref_2402_);
v___x_2404_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; 
lean_inc_ref(v___x_2404_);
lean_inc_ref(v_stx_2383_);
v___x_2405_ = l_Lean_Macro_expandMacro_x3f(v_stx_2383_, v___x_2404_, v_a_2386_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
if (lean_obj_tag(v_a_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v___x_2404_);
v_a_2407_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2405_, 0);
lean_dec(v_unused_2453_);
v___x_2409_ = v___x_2405_;
v_isShared_2410_ = v_isSharedCheck_2452_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2405_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2452_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_nat_dec_eq(v_currRecDepth_2396_, v_maxRecDepth_2397_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2443_; 
lean_inc_ref(v_args_2389_);
lean_inc(v_kind_2388_);
lean_inc(v_info_2387_);
lean_del_object(v___x_2409_);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_stx_2383_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; lean_object* v_unused_2445_; lean_object* v_unused_2446_; 
v_unused_2444_ = lean_ctor_get(v_stx_2383_, 2);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_stx_2383_, 1);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_stx_2383_, 0);
lean_dec(v_unused_2446_);
v___x_2413_ = v_stx_2383_;
v_isShared_2414_ = v_isSharedCheck_2443_;
goto v_resetjp_2412_;
}
else
{
lean_dec(v_stx_2383_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2443_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; size_t v_sz_2418_; size_t v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_add(v_currRecDepth_2396_, v___x_2415_);
lean_dec(v_currRecDepth_2396_);
v___x_2417_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2417_, 0, v_methods_2393_);
lean_ctor_set(v___x_2417_, 1, v_quotContext_2394_);
lean_ctor_set(v___x_2417_, 2, v_currMacroScope_2395_);
lean_ctor_set(v___x_2417_, 3, v___x_2416_);
lean_ctor_set(v___x_2417_, 4, v_maxRecDepth_2397_);
lean_ctor_set(v___x_2417_, 5, v_ref_2402_);
v_sz_2418_ = lean_array_size(v_args_2389_);
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = lean_unbox(v___x_2390_);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2420_, v_sz_2418_, v___x_2419_, v_args_2389_, v___x_2417_, v_a_2407_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2433_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_a_2423_ = lean_ctor_get(v___x_2421_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2425_ = v___x_2421_;
v_isShared_2426_ = v_isSharedCheck_2433_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2433_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 2, v_a_2422_);
v___x_2428_ = v___x_2413_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_info_2387_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_kind_2388_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_a_2422_);
v___x_2428_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2430_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2428_);
v___x_2430_ = v___x_2425_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_a_2423_);
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
lean_object* v_a_2434_; lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_del_object(v___x_2413_);
lean_dec(v_kind_2388_);
lean_dec(v_info_2387_);
v_a_2434_ = lean_ctor_get(v___x_2421_, 0);
v_a_2435_ = lean_ctor_get(v___x_2421_, 1);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2421_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_inc(v_a_2434_);
lean_dec(v___x_2421_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2434_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
lean_dec(v_ref_2402_);
lean_dec(v_maxRecDepth_2397_);
lean_dec(v_currRecDepth_2396_);
lean_dec(v_currMacroScope_2395_);
lean_dec(v_quotContext_2394_);
lean_dec(v_methods_2393_);
v___x_2447_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_stx_2383_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set_tag(v___x_2409_, 1);
lean_ctor_set(v___x_2409_, 0, v___x_2448_);
v___x_2450_ = v___x_2409_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_a_2407_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v_val_2455_; lean_object* v___f_2456_; 
lean_dec(v_ref_2402_);
lean_dec(v_maxRecDepth_2397_);
lean_dec(v_currRecDepth_2396_);
lean_dec(v_currMacroScope_2395_);
lean_dec(v_quotContext_2394_);
lean_dec(v_methods_2393_);
lean_dec_ref(v_stx_2383_);
v_a_2454_ = lean_ctor_get(v___x_2405_, 1);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2405_);
v_val_2455_ = lean_ctor_get(v_a_2406_, 0);
lean_inc(v_val_2455_);
lean_dec_ref(v_a_2406_);
v___f_2456_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2456_, 0, v___x_2390_);
v_stx_2383_ = v_val_2455_;
v_p_2384_ = v___f_2456_;
v_a_2385_ = v___x_2404_;
v_a_2386_ = v_a_2454_;
goto _start;
}
}
else
{
lean_object* v_a_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v___x_2404_);
lean_dec(v_ref_2402_);
lean_dec(v_maxRecDepth_2397_);
lean_dec(v_currRecDepth_2396_);
lean_dec(v_currMacroScope_2395_);
lean_dec(v_quotContext_2394_);
lean_dec(v_methods_2393_);
lean_dec_ref(v_stx_2383_);
v_a_2458_ = lean_ctor_get(v___x_2405_, 0);
v_a_2459_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2405_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_inc(v_a_2458_);
lean_dec(v___x_2405_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2458_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2469_; 
lean_dec_ref(v_a_2385_);
lean_dec_ref(v_p_2384_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_stx_2383_);
lean_ctor_set(v___x_2469_, 1, v_a_2386_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2470_, size_t v_sz_2471_, size_t v_i_2472_, lean_object* v_bs_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_usize_dec_lt(v_i_2472_, v_sz_2471_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
lean_dec_ref(v___y_2474_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v_bs_2473_);
lean_ctor_set(v___x_2477_, 1, v___y_2475_);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v_v_2480_; lean_object* v___x_2481_; 
v___x_2478_ = lean_box(v___x_2470_);
v___f_2479_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2479_, 0, v___x_2478_);
v_v_2480_ = lean_array_uget_borrowed(v_bs_2473_, v_i_2472_);
lean_inc_ref(v___y_2474_);
lean_inc(v_v_2480_);
v___x_2481_ = l_Lean_expandMacros(v_v_2480_, v___f_2479_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v_a_2483_; lean_object* v___x_2484_; lean_object* v_bs_x27_2485_; size_t v___x_2486_; size_t v___x_2487_; lean_object* v___x_2488_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
v_a_2483_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_a_2483_);
lean_dec_ref(v___x_2481_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v_bs_x27_2485_ = lean_array_uset(v_bs_2473_, v_i_2472_, v___x_2484_);
v___x_2486_ = ((size_t)1ULL);
v___x_2487_ = lean_usize_add(v_i_2472_, v___x_2486_);
v___x_2488_ = lean_array_uset(v_bs_x27_2485_, v_i_2472_, v_a_2482_);
v_i_2472_ = v___x_2487_;
v_bs_2473_ = v___x_2488_;
v___y_2475_ = v_a_2483_;
goto _start;
}
else
{
lean_object* v_a_2490_; lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_bs_2473_);
v_a_2490_ = lean_ctor_get(v___x_2481_, 0);
v_a_2491_ = lean_ctor_get(v___x_2481_, 1);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2481_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_inc(v_a_2490_);
lean_dec(v___x_2481_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2490_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2499_, lean_object* v_sz_2500_, lean_object* v_i_2501_, lean_object* v_bs_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v___x_1867__boxed_2505_; size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v___x_1867__boxed_2505_ = lean_unbox(v___x_2499_);
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2500_);
lean_dec(v_sz_2500_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2501_);
lean_dec(v_i_2501_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1867__boxed_2505_, v_sz_boxed_2506_, v_i_boxed_2507_, v_bs_2502_, v___y_2503_, v___y_2504_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2509_, lean_object* v_val_2510_, uint8_t v_canonical_2511_){
_start:
{
lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2512_ = l_Lean_SourceInfo_fromRef(v_src_2509_, v_canonical_2511_);
v___x_2513_ = 1;
lean_inc(v_val_2510_);
v___x_2514_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2510_, v___x_2513_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = lean_string_utf8_byte_size(v___x_2514_);
v___x_2517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2514_);
lean_ctor_set(v___x_2517_, 1, v___x_2515_);
lean_ctor_set(v___x_2517_, 2, v___x_2516_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2512_);
lean_ctor_set(v___x_2519_, 1, v___x_2517_);
lean_ctor_set(v___x_2519_, 2, v_val_2510_);
lean_ctor_set(v___x_2519_, 3, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2520_, lean_object* v_val_2521_, lean_object* v_canonical_2522_){
_start:
{
uint8_t v_canonical_boxed_2523_; lean_object* v_res_2524_; 
v_canonical_boxed_2523_ = lean_unbox(v_canonical_2522_);
v_res_2524_ = l_Lean_mkIdentFrom(v_src_2520_, v_val_2521_, v_canonical_boxed_2523_);
lean_dec(v_src_2520_);
return v_res_2524_;
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
LEAN_EXPORT lean_object* lean_mk_syntax_ident(lean_object* v_val_2636_){
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
lean_dec_ref(v_arg_2710_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object* v_sep_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(v___x_2797_, 0, v_sep_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2798_, lean_object* v_elems_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2798_, v_elems_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2801_, lean_object* v_elems_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2801_, v_elems_2802_);
lean_dec_ref(v_elems_2802_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2804_, lean_object* v_sep_2805_, lean_object* v_elems_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2805_, v_elems_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2808_, lean_object* v_sep_2809_, lean_object* v_elems_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2808_, v_sep_2809_, v_elems_2810_);
lean_dec_ref(v_elems_2810_);
lean_dec(v_k_2808_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2812_, lean_object* v_sep_2813_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2814_, 0, v_k_2812_);
lean_closure_set(v___x_2814_, 1, v_sep_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2823_ = lean_array_get_size(v_x_2822_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_nat_dec_eq(v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2826_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2827_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2828_ = lean_box(2);
v___x_2829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2827_);
lean_ctor_set(v___x_2829_, 2, v_x_2822_);
v___x_2830_ = lean_unsigned_to_nat(2u);
v___x_2831_ = lean_mk_empty_array_with_capacity(v___x_2830_);
v___x_2832_ = lean_array_push(v___x_2831_, v_fn_2821_);
v___x_2833_ = lean_array_push(v___x_2832_, v___x_2829_);
v___x_2834_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2828_);
lean_ctor_set(v___x_2834_, 1, v___x_2826_);
lean_ctor_set(v___x_2834_, 2, v___x_2833_);
return v___x_2834_;
}
else
{
lean_dec_ref(v_x_2822_);
return v_fn_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2835_, lean_object* v_args_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = l_Lean_mkCIdent(v_fn_2835_);
v___x_2838_ = l_Lean_Syntax_mkApp(v___x_2837_, v_args_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2839_, lean_object* v_val_2840_, lean_object* v_info_2841_){
_start:
{
lean_object* v_atom_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_atom_2842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2842_, 0, v_info_2841_);
lean_ctor_set(v_atom_2842_, 1, v_val_2840_);
v___x_2843_ = lean_unsigned_to_nat(1u);
v___x_2844_ = lean_mk_empty_array_with_capacity(v___x_2843_);
v___x_2845_ = lean_array_push(v___x_2844_, v_atom_2842_);
v___x_2846_ = lean_box(2);
v___x_2847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v_kind_2839_);
lean_ctor_set(v___x_2847_, 2, v___x_2845_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2851_, lean_object* v_info_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2853_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2854_ = l_Char_quote(v_val_2851_);
v___x_2855_ = l_Lean_Syntax_mkLit(v___x_2853_, v___x_2854_, v_info_2852_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2856_, lean_object* v_info_2857_){
_start:
{
uint32_t v_val_boxed_2858_; lean_object* v_res_2859_; 
v_val_boxed_2858_ = lean_unbox_uint32(v_val_2856_);
lean_dec(v_val_2856_);
v_res_2859_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2858_, v_info_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2863_, lean_object* v_info_2864_){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2866_ = l_String_quote(v_val_2863_);
v___x_2867_ = l_Lean_Syntax_mkLit(v___x_2865_, v___x_2866_, v_info_2864_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2871_, lean_object* v_info_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2874_ = l_Lean_Syntax_mkLit(v___x_2873_, v_val_2871_, v_info_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2875_, lean_object* v_info_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2878_ = l_Nat_reprFast(v_val_2875_);
v___x_2879_ = l_Lean_Syntax_mkLit(v___x_2877_, v___x_2878_, v_info_2876_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2883_, lean_object* v_info_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2886_ = l_Lean_Syntax_mkLit(v___x_2885_, v_val_2883_, v_info_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2890_, lean_object* v_info_2891_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2893_ = l_Lean_Syntax_mkLit(v___x_2892_, v_val_2890_, v_info_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2894_, lean_object* v_i_2895_, lean_object* v_val_2896_){
_start:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_string_utf8_at_end(v_s_2894_, v_i_2895_);
if (v___x_2897_ == 0)
{
uint32_t v_c_2898_; uint32_t v___x_2899_; uint8_t v___x_2900_; 
v_c_2898_ = lean_string_utf8_get(v_s_2894_, v_i_2895_);
v___x_2899_ = 48;
v___x_2900_ = lean_uint32_dec_eq(v_c_2898_, v___x_2899_);
if (v___x_2900_ == 0)
{
uint32_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 49;
v___x_2902_ = lean_uint32_dec_eq(v_c_2898_, v___x_2901_);
if (v___x_2902_ == 0)
{
uint32_t v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = 95;
v___x_2904_ = lean_uint32_dec_eq(v_c_2898_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_val_2896_);
lean_dec(v_i_2895_);
v___x_2905_ = lean_box(0);
return v___x_2905_;
}
else
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_string_utf8_next(v_s_2894_, v_i_2895_);
lean_dec(v_i_2895_);
v_i_2895_ = v___x_2906_;
goto _start;
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2908_ = lean_string_utf8_next(v_s_2894_, v_i_2895_);
lean_dec(v_i_2895_);
v___x_2909_ = lean_unsigned_to_nat(2u);
v___x_2910_ = lean_nat_mul(v___x_2909_, v_val_2896_);
lean_dec(v_val_2896_);
v___x_2911_ = lean_unsigned_to_nat(1u);
v___x_2912_ = lean_nat_add(v___x_2910_, v___x_2911_);
lean_dec(v___x_2910_);
v_i_2895_ = v___x_2908_;
v_val_2896_ = v___x_2912_;
goto _start;
}
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_string_utf8_next(v_s_2894_, v_i_2895_);
lean_dec(v_i_2895_);
v___x_2915_ = lean_unsigned_to_nat(2u);
v___x_2916_ = lean_nat_mul(v___x_2915_, v_val_2896_);
lean_dec(v_val_2896_);
v_i_2895_ = v___x_2914_;
v_val_2896_ = v___x_2916_;
goto _start;
}
}
else
{
lean_object* v___x_2918_; 
lean_dec(v_i_2895_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_val_2896_);
return v___x_2918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2919_, lean_object* v_i_2920_, lean_object* v_val_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2919_, v_i_2920_, v_val_2921_);
lean_dec_ref(v_s_2919_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2923_, lean_object* v_i_2924_, lean_object* v_val_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_string_utf8_at_end(v_s_2923_, v_i_2924_);
if (v___x_2926_ == 0)
{
uint32_t v_c_2927_; uint8_t v___y_2929_; uint32_t v___x_2943_; uint8_t v___x_2944_; 
v_c_2927_ = lean_string_utf8_get(v_s_2923_, v_i_2924_);
v___x_2943_ = 48;
v___x_2944_ = lean_uint32_dec_le(v___x_2943_, v_c_2927_);
if (v___x_2944_ == 0)
{
v___y_2929_ = v___x_2944_;
goto v___jp_2928_;
}
else
{
uint32_t v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = 55;
v___x_2946_ = lean_uint32_dec_le(v_c_2927_, v___x_2945_);
v___y_2929_ = v___x_2946_;
goto v___jp_2928_;
}
v___jp_2928_:
{
if (v___y_2929_ == 0)
{
uint32_t v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = 95;
v___x_2931_ = lean_uint32_dec_eq(v_c_2927_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
lean_dec(v_val_2925_);
lean_dec(v_i_2924_);
v___x_2932_ = lean_box(0);
return v___x_2932_;
}
else
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_string_utf8_next(v_s_2923_, v_i_2924_);
lean_dec(v_i_2924_);
v_i_2924_ = v___x_2933_;
goto _start;
}
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2935_ = lean_string_utf8_next(v_s_2923_, v_i_2924_);
lean_dec(v_i_2924_);
v___x_2936_ = lean_unsigned_to_nat(8u);
v___x_2937_ = lean_nat_mul(v___x_2936_, v_val_2925_);
lean_dec(v_val_2925_);
v___x_2938_ = lean_uint32_to_nat(v_c_2927_);
v___x_2939_ = lean_nat_add(v___x_2937_, v___x_2938_);
lean_dec(v___x_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_unsigned_to_nat(48u);
v___x_2941_ = lean_nat_sub(v___x_2939_, v___x_2940_);
lean_dec(v___x_2939_);
v_i_2924_ = v___x_2935_;
v_val_2925_ = v___x_2941_;
goto _start;
}
}
}
else
{
lean_object* v___x_2947_; 
lean_dec(v_i_2924_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_val_2925_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2948_, lean_object* v_i_2949_, lean_object* v_val_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2948_, v_i_2949_, v_val_2950_);
lean_dec_ref(v_s_2948_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2952_, lean_object* v_i_2953_){
_start:
{
uint32_t v_c_2954_; lean_object* v_i_2955_; uint8_t v___y_2957_; uint8_t v___y_2967_; uint8_t v___y_2980_; uint32_t v___x_2990_; uint8_t v___x_2991_; 
v_c_2954_ = lean_string_utf8_get(v_s_2952_, v_i_2953_);
v_i_2955_ = lean_string_utf8_next(v_s_2952_, v_i_2953_);
v___x_2990_ = 48;
v___x_2991_ = lean_uint32_dec_le(v___x_2990_, v_c_2954_);
if (v___x_2991_ == 0)
{
v___y_2980_ = v___x_2991_;
goto v___jp_2979_;
}
else
{
uint32_t v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = 57;
v___x_2993_ = lean_uint32_dec_le(v_c_2954_, v___x_2992_);
v___y_2980_ = v___x_2993_;
goto v___jp_2979_;
}
v___jp_2956_:
{
if (v___y_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec(v_i_2955_);
v___x_2958_ = lean_box(0);
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2959_ = lean_unsigned_to_nat(10u);
v___x_2960_ = lean_uint32_to_nat(v_c_2954_);
v___x_2961_ = lean_nat_add(v___x_2959_, v___x_2960_);
lean_dec(v___x_2960_);
v___x_2962_ = lean_unsigned_to_nat(65u);
v___x_2963_ = lean_nat_sub(v___x_2961_, v___x_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v_i_2955_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
v___jp_2966_:
{
if (v___y_2967_ == 0)
{
uint32_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = 65;
v___x_2969_ = lean_uint32_dec_le(v___x_2968_, v_c_2954_);
if (v___x_2969_ == 0)
{
v___y_2957_ = v___x_2969_;
goto v___jp_2956_;
}
else
{
uint32_t v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = 70;
v___x_2971_ = lean_uint32_dec_le(v_c_2954_, v___x_2970_);
v___y_2957_ = v___x_2971_;
goto v___jp_2956_;
}
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2972_ = lean_unsigned_to_nat(10u);
v___x_2973_ = lean_uint32_to_nat(v_c_2954_);
v___x_2974_ = lean_nat_add(v___x_2972_, v___x_2973_);
lean_dec(v___x_2973_);
v___x_2975_ = lean_unsigned_to_nat(97u);
v___x_2976_ = lean_nat_sub(v___x_2974_, v___x_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v_i_2955_);
v___x_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
v___jp_2979_:
{
if (v___y_2980_ == 0)
{
uint32_t v___x_2981_; uint8_t v___x_2982_; 
v___x_2981_ = 97;
v___x_2982_ = lean_uint32_dec_le(v___x_2981_, v_c_2954_);
if (v___x_2982_ == 0)
{
v___y_2967_ = v___x_2982_;
goto v___jp_2966_;
}
else
{
uint32_t v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = 102;
v___x_2984_ = lean_uint32_dec_le(v_c_2954_, v___x_2983_);
v___y_2967_ = v___x_2984_;
goto v___jp_2966_;
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2985_ = lean_uint32_to_nat(v_c_2954_);
v___x_2986_ = lean_unsigned_to_nat(48u);
v___x_2987_ = lean_nat_sub(v___x_2985_, v___x_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v_i_2955_);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2994_, lean_object* v_i_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2994_, v_i_2995_);
lean_dec(v_i_2995_);
lean_dec_ref(v_s_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2997_, lean_object* v_i_2998_, lean_object* v_val_2999_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_string_utf8_at_end(v_s_2997_, v_i_2998_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2997_, v_i_2998_);
if (lean_obj_tag(v___x_3001_) == 0)
{
uint32_t v___x_3002_; uint32_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_string_utf8_get(v_s_2997_, v_i_2998_);
v___x_3003_ = 95;
v___x_3004_ = lean_uint32_dec_eq(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
lean_dec(v_val_2999_);
lean_dec(v_i_2998_);
v___x_3005_ = lean_box(0);
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_string_utf8_next(v_s_2997_, v_i_2998_);
lean_dec(v_i_2998_);
v_i_2998_ = v___x_3006_;
goto _start;
}
}
else
{
lean_object* v_val_3008_; lean_object* v_fst_3009_; lean_object* v_snd_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec(v_i_2998_);
v_val_3008_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_val_3008_);
lean_dec_ref(v___x_3001_);
v_fst_3009_ = lean_ctor_get(v_val_3008_, 0);
lean_inc(v_fst_3009_);
v_snd_3010_ = lean_ctor_get(v_val_3008_, 1);
lean_inc(v_snd_3010_);
lean_dec(v_val_3008_);
v___x_3011_ = lean_unsigned_to_nat(16u);
v___x_3012_ = lean_nat_mul(v___x_3011_, v_val_2999_);
lean_dec(v_val_2999_);
v___x_3013_ = lean_nat_add(v___x_3012_, v_fst_3009_);
lean_dec(v_fst_3009_);
lean_dec(v___x_3012_);
v_i_2998_ = v_snd_3010_;
v_val_2999_ = v___x_3013_;
goto _start;
}
}
else
{
lean_object* v___x_3015_; 
lean_dec(v_i_2998_);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_val_2999_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3016_, lean_object* v_i_3017_, lean_object* v_val_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3016_, v_i_3017_, v_val_3018_);
lean_dec_ref(v_s_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3020_, lean_object* v_i_3021_, lean_object* v_val_3022_){
_start:
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_string_utf8_at_end(v_s_3020_, v_i_3021_);
if (v___x_3023_ == 0)
{
uint32_t v_c_3024_; uint8_t v___y_3026_; uint32_t v___x_3040_; uint8_t v___x_3041_; 
v_c_3024_ = lean_string_utf8_get(v_s_3020_, v_i_3021_);
v___x_3040_ = 48;
v___x_3041_ = lean_uint32_dec_le(v___x_3040_, v_c_3024_);
if (v___x_3041_ == 0)
{
v___y_3026_ = v___x_3041_;
goto v___jp_3025_;
}
else
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = 57;
v___x_3043_ = lean_uint32_dec_le(v_c_3024_, v___x_3042_);
v___y_3026_ = v___x_3043_;
goto v___jp_3025_;
}
v___jp_3025_:
{
if (v___y_3026_ == 0)
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 95;
v___x_3028_ = lean_uint32_dec_eq(v_c_3024_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
lean_dec(v_val_3022_);
lean_dec(v_i_3021_);
v___x_3029_ = lean_box(0);
return v___x_3029_;
}
else
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_string_utf8_next(v_s_3020_, v_i_3021_);
lean_dec(v_i_3021_);
v_i_3021_ = v___x_3030_;
goto _start;
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3032_ = lean_string_utf8_next(v_s_3020_, v_i_3021_);
lean_dec(v_i_3021_);
v___x_3033_ = lean_unsigned_to_nat(10u);
v___x_3034_ = lean_nat_mul(v___x_3033_, v_val_3022_);
lean_dec(v_val_3022_);
v___x_3035_ = lean_uint32_to_nat(v_c_3024_);
v___x_3036_ = lean_nat_add(v___x_3034_, v___x_3035_);
lean_dec(v___x_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_unsigned_to_nat(48u);
v___x_3038_ = lean_nat_sub(v___x_3036_, v___x_3037_);
lean_dec(v___x_3036_);
v_i_3021_ = v___x_3032_;
v_val_3022_ = v___x_3038_;
goto _start;
}
}
}
else
{
lean_object* v___x_3044_; 
lean_dec(v_i_3021_);
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_val_3022_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3045_, lean_object* v_i_3046_, lean_object* v_val_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3045_, v_i_3046_, v_val_3047_);
lean_dec_ref(v_s_3045_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3051_){
_start:
{
lean_object* v_len_3052_; lean_object* v___x_3053_; uint8_t v___y_3055_; uint8_t v___y_3068_; uint8_t v___x_3071_; 
v_len_3052_ = lean_string_length(v_s_3051_);
v___x_3053_ = lean_unsigned_to_nat(0u);
v___x_3071_ = lean_nat_dec_eq(v_len_3052_, v___x_3053_);
if (v___x_3071_ == 0)
{
uint32_t v_c_3072_; uint32_t v___x_3073_; uint8_t v___x_3074_; 
v_c_3072_ = lean_string_utf8_get(v_s_3051_, v___x_3053_);
v___x_3073_ = 48;
v___x_3074_ = lean_uint32_dec_eq(v_c_3072_, v___x_3073_);
if (v___x_3074_ == 0)
{
uint8_t v___x_3075_; 
lean_dec(v_len_3052_);
v___x_3075_ = lean_uint32_dec_le(v___x_3073_, v_c_3072_);
if (v___x_3075_ == 0)
{
v___y_3068_ = v___x_3075_;
goto v___jp_3067_;
}
else
{
uint32_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = 57;
v___x_3077_ = lean_uint32_dec_le(v_c_3072_, v___x_3076_);
v___y_3068_ = v___x_3077_;
goto v___jp_3067_;
}
}
else
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = lean_unsigned_to_nat(1u);
v___x_3079_ = lean_nat_dec_eq(v_len_3052_, v___x_3078_);
lean_dec(v_len_3052_);
if (v___x_3079_ == 0)
{
uint32_t v_c_3080_; uint32_t v___x_3081_; uint8_t v___x_3082_; 
v_c_3080_ = lean_string_utf8_get(v_s_3051_, v___x_3078_);
v___x_3081_ = 120;
v___x_3082_ = lean_uint32_dec_eq(v_c_3080_, v___x_3081_);
if (v___x_3082_ == 0)
{
uint32_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = 88;
v___x_3084_ = lean_uint32_dec_eq(v_c_3080_, v___x_3083_);
if (v___x_3084_ == 0)
{
uint32_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = 98;
v___x_3086_ = lean_uint32_dec_eq(v_c_3080_, v___x_3085_);
if (v___x_3086_ == 0)
{
uint32_t v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = 66;
v___x_3088_ = lean_uint32_dec_eq(v_c_3080_, v___x_3087_);
if (v___x_3088_ == 0)
{
uint32_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = 111;
v___x_3090_ = lean_uint32_dec_eq(v_c_3080_, v___x_3089_);
if (v___x_3090_ == 0)
{
uint32_t v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = 79;
v___x_3092_ = lean_uint32_dec_eq(v_c_3080_, v___x_3091_);
if (v___x_3092_ == 0)
{
uint8_t v___x_3093_; 
v___x_3093_ = lean_uint32_dec_le(v___x_3073_, v_c_3080_);
if (v___x_3093_ == 0)
{
v___y_3055_ = v___x_3093_;
goto v___jp_3054_;
}
else
{
uint32_t v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = 57;
v___x_3095_ = lean_uint32_dec_le(v_c_3080_, v___x_3094_);
v___y_3055_ = v___x_3095_;
goto v___jp_3054_;
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
goto v___jp_3061_;
}
}
else
{
goto v___jp_3061_;
}
}
else
{
goto v___jp_3064_;
}
}
else
{
goto v___jp_3064_;
}
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3096_;
}
}
}
else
{
lean_object* v___x_3097_; 
lean_dec(v_len_3052_);
v___x_3097_ = lean_box(0);
return v___x_3097_;
}
v___jp_3054_:
{
if (v___y_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_box(0);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3051_, v___x_3053_, v___x_3053_);
return v___x_3057_;
}
}
v___jp_3058_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_unsigned_to_nat(2u);
v___x_3060_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3051_, v___x_3059_, v___x_3053_);
return v___x_3060_;
}
v___jp_3061_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_unsigned_to_nat(2u);
v___x_3063_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3051_, v___x_3062_, v___x_3053_);
return v___x_3063_;
}
v___jp_3064_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = lean_unsigned_to_nat(2u);
v___x_3066_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3051_, v___x_3065_, v___x_3053_);
return v___x_3066_;
}
v___jp_3067_:
{
if (v___y_3068_ == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_box(0);
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3051_, v___x_3053_, v___x_3053_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3098_);
lean_dec_ref(v_s_3098_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3100_, lean_object* v_stx_3101_){
_start:
{
if (lean_obj_tag(v_stx_3101_) == 1)
{
lean_object* v_kind_3102_; lean_object* v_args_3103_; uint8_t v___x_3104_; 
v_kind_3102_ = lean_ctor_get(v_stx_3101_, 1);
v_args_3103_ = lean_ctor_get(v_stx_3101_, 2);
v___x_3104_ = lean_name_eq(v_kind_3102_, v_litKind_3100_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_box(0);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_array_get_size(v_args_3103_);
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = lean_nat_dec_eq(v___x_3106_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_box(0);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_array_fget_borrowed(v_args_3103_, v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 2)
{
lean_object* v_val_3112_; lean_object* v___x_3113_; 
v_val_3112_ = lean_ctor_get(v___x_3111_, 1);
lean_inc_ref(v_val_3112_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_val_3112_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_box(0);
return v___x_3114_;
}
}
}
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_box(0);
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3116_, lean_object* v_stx_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_Syntax_isLit_x3f(v_litKind_3116_, v_stx_3117_);
lean_dec(v_stx_3117_);
lean_dec(v_litKind_3116_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3119_, lean_object* v_stx_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_Syntax_isLit_x3f(v_litKind_3119_, v_stx_3120_);
if (lean_obj_tag(v___x_3121_) == 1)
{
lean_object* v_val_3122_; lean_object* v___x_3123_; 
v_val_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_val_3122_);
lean_dec_ref(v___x_3121_);
v___x_3123_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3122_);
lean_dec(v_val_3122_);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; 
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
return v___x_3124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3125_, lean_object* v_stx_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3125_, v_stx_3126_);
lean_dec(v_stx_3126_);
lean_dec(v_litKind_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3128_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3130_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3129_, v_s_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Syntax_isNatLit_x3f(v_s_3131_);
lean_dec(v_s_3131_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3138_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3137_, v_s_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3139_);
lean_dec(v_s_3139_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3141_, lean_object* v_i_3142_, lean_object* v_val_3143_, lean_object* v_e_3144_, uint8_t v_sign_3145_, lean_object* v_exp_3146_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_string_utf8_at_end(v_s_3141_, v_i_3142_);
if (v___x_3147_ == 0)
{
uint32_t v_c_3148_; uint8_t v___y_3150_; uint32_t v___x_3164_; uint8_t v___x_3165_; 
v_c_3148_ = lean_string_utf8_get(v_s_3141_, v_i_3142_);
v___x_3164_ = 48;
v___x_3165_ = lean_uint32_dec_le(v___x_3164_, v_c_3148_);
if (v___x_3165_ == 0)
{
v___y_3150_ = v___x_3165_;
goto v___jp_3149_;
}
else
{
uint32_t v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = 57;
v___x_3167_ = lean_uint32_dec_le(v_c_3148_, v___x_3166_);
v___y_3150_ = v___x_3167_;
goto v___jp_3149_;
}
v___jp_3149_:
{
if (v___y_3150_ == 0)
{
uint32_t v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = 95;
v___x_3152_ = lean_uint32_dec_eq(v_c_3148_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec(v_exp_3146_);
lean_dec(v_val_3143_);
lean_dec(v_i_3142_);
v___x_3153_ = lean_box(0);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_string_utf8_next(v_s_3141_, v_i_3142_);
lean_dec(v_i_3142_);
v_i_3142_ = v___x_3154_;
goto _start;
}
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3156_ = lean_string_utf8_next(v_s_3141_, v_i_3142_);
lean_dec(v_i_3142_);
v___x_3157_ = lean_unsigned_to_nat(10u);
v___x_3158_ = lean_nat_mul(v___x_3157_, v_exp_3146_);
lean_dec(v_exp_3146_);
v___x_3159_ = lean_uint32_to_nat(v_c_3148_);
v___x_3160_ = lean_nat_add(v___x_3158_, v___x_3159_);
lean_dec(v___x_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_unsigned_to_nat(48u);
v___x_3162_ = lean_nat_sub(v___x_3160_, v___x_3161_);
lean_dec(v___x_3160_);
v_i_3142_ = v___x_3156_;
v_exp_3146_ = v___x_3162_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3142_);
if (v_sign_3145_ == 0)
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_nat_dec_le(v_e_3144_, v_exp_3146_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3169_ = lean_nat_sub(v_e_3144_, v_exp_3146_);
lean_dec(v_exp_3146_);
v___x_3170_ = lean_box(v___x_3147_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3169_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_val_3143_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3174_ = lean_nat_sub(v_exp_3146_, v_e_3144_);
lean_dec(v_exp_3146_);
v___x_3175_ = lean_box(v_sign_3145_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3174_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_val_3143_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3179_ = lean_nat_add(v_exp_3146_, v_e_3144_);
lean_dec(v_exp_3146_);
v___x_3180_ = lean_box(v_sign_3145_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3179_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_val_3143_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3184_, lean_object* v_i_3185_, lean_object* v_val_3186_, lean_object* v_e_3187_, lean_object* v_sign_3188_, lean_object* v_exp_3189_){
_start:
{
uint8_t v_sign_boxed_3190_; lean_object* v_res_3191_; 
v_sign_boxed_3190_ = lean_unbox(v_sign_3188_);
v_res_3191_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3184_, v_i_3185_, v_val_3186_, v_e_3187_, v_sign_boxed_3190_, v_exp_3189_);
lean_dec(v_e_3187_);
lean_dec_ref(v_s_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3192_, lean_object* v_i_3193_, lean_object* v_val_3194_, lean_object* v_e_3195_){
_start:
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_string_utf8_at_end(v_s_3192_, v_i_3193_);
if (v___x_3196_ == 0)
{
uint32_t v_c_3197_; uint32_t v___x_3198_; uint8_t v___x_3199_; 
v_c_3197_ = lean_string_utf8_get(v_s_3192_, v_i_3193_);
v___x_3198_ = 45;
v___x_3199_ = lean_uint32_dec_eq(v_c_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
uint32_t v___x_3200_; uint8_t v___x_3201_; 
v___x_3200_ = 43;
v___x_3201_ = lean_uint32_dec_eq(v_c_3197_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3192_, v_i_3193_, v_val_3194_, v_e_3195_, v___x_3201_, v___x_3202_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_string_utf8_next(v_s_3192_, v_i_3193_);
lean_dec(v_i_3193_);
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3192_, v___x_3204_, v_val_3194_, v_e_3195_, v___x_3199_, v___x_3205_);
return v___x_3206_;
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_string_utf8_next(v_s_3192_, v_i_3193_);
lean_dec(v_i_3193_);
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3192_, v___x_3207_, v_val_3194_, v_e_3195_, v___x_3199_, v___x_3208_);
return v___x_3209_;
}
}
else
{
lean_object* v___x_3210_; 
lean_dec(v_val_3194_);
lean_dec(v_i_3193_);
v___x_3210_ = lean_box(0);
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3211_, lean_object* v_i_3212_, lean_object* v_val_3213_, lean_object* v_e_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3211_, v_i_3212_, v_val_3213_, v_e_3214_);
lean_dec(v_e_3214_);
lean_dec_ref(v_s_3211_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3216_, lean_object* v_i_3217_, lean_object* v_val_3218_, lean_object* v_e_3219_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_string_utf8_at_end(v_s_3216_, v_i_3217_);
if (v___x_3223_ == 0)
{
uint32_t v_c_3224_; uint8_t v___y_3226_; uint32_t v___x_3246_; uint8_t v___x_3247_; 
v_c_3224_ = lean_string_utf8_get(v_s_3216_, v_i_3217_);
v___x_3246_ = 48;
v___x_3247_ = lean_uint32_dec_le(v___x_3246_, v_c_3224_);
if (v___x_3247_ == 0)
{
v___y_3226_ = v___x_3247_;
goto v___jp_3225_;
}
else
{
uint32_t v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = 57;
v___x_3249_ = lean_uint32_dec_le(v_c_3224_, v___x_3248_);
v___y_3226_ = v___x_3249_;
goto v___jp_3225_;
}
v___jp_3225_:
{
if (v___y_3226_ == 0)
{
uint32_t v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = 95;
v___x_3228_ = lean_uint32_dec_eq(v_c_3224_, v___x_3227_);
if (v___x_3228_ == 0)
{
uint32_t v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = 101;
v___x_3230_ = lean_uint32_dec_eq(v_c_3224_, v___x_3229_);
if (v___x_3230_ == 0)
{
uint32_t v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = 69;
v___x_3232_ = lean_uint32_dec_eq(v_c_3224_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_dec(v_e_3219_);
lean_dec(v_val_3218_);
lean_dec(v_i_3217_);
v___x_3233_ = lean_box(0);
return v___x_3233_;
}
else
{
goto v___jp_3220_;
}
}
else
{
goto v___jp_3220_;
}
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_string_utf8_next(v_s_3216_, v_i_3217_);
lean_dec(v_i_3217_);
v_i_3217_ = v___x_3234_;
goto _start;
}
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3236_ = lean_string_utf8_next(v_s_3216_, v_i_3217_);
lean_dec(v_i_3217_);
v___x_3237_ = lean_unsigned_to_nat(10u);
v___x_3238_ = lean_nat_mul(v___x_3237_, v_val_3218_);
lean_dec(v_val_3218_);
v___x_3239_ = lean_uint32_to_nat(v_c_3224_);
v___x_3240_ = lean_nat_add(v___x_3238_, v___x_3239_);
lean_dec(v___x_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_unsigned_to_nat(48u);
v___x_3242_ = lean_nat_sub(v___x_3240_, v___x_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_nat_add(v_e_3219_, v___x_3243_);
lean_dec(v_e_3219_);
v_i_3217_ = v___x_3236_;
v_val_3218_ = v___x_3242_;
v_e_3219_ = v___x_3244_;
goto _start;
}
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_i_3217_);
v___x_3250_ = lean_box(v___x_3223_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v_e_3219_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_val_3218_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
v___jp_3220_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_string_utf8_next(v_s_3216_, v_i_3217_);
lean_dec(v_i_3217_);
v___x_3222_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3216_, v___x_3221_, v_val_3218_, v_e_3219_);
lean_dec(v_e_3219_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3254_, lean_object* v_i_3255_, lean_object* v_val_3256_, lean_object* v_e_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3254_, v_i_3255_, v_val_3256_, v_e_3257_);
lean_dec_ref(v_s_3254_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3259_, lean_object* v_i_3260_, lean_object* v_val_3261_){
_start:
{
uint8_t v___x_3266_; 
v___x_3266_ = lean_string_utf8_at_end(v_s_3259_, v_i_3260_);
if (v___x_3266_ == 0)
{
uint32_t v_c_3267_; uint8_t v___y_3269_; uint32_t v___x_3292_; uint8_t v___x_3293_; 
v_c_3267_ = lean_string_utf8_get(v_s_3259_, v_i_3260_);
v___x_3292_ = 48;
v___x_3293_ = lean_uint32_dec_le(v___x_3292_, v_c_3267_);
if (v___x_3293_ == 0)
{
v___y_3269_ = v___x_3293_;
goto v___jp_3268_;
}
else
{
uint32_t v___x_3294_; uint8_t v___x_3295_; 
v___x_3294_ = 57;
v___x_3295_ = lean_uint32_dec_le(v_c_3267_, v___x_3294_);
v___y_3269_ = v___x_3295_;
goto v___jp_3268_;
}
v___jp_3268_:
{
if (v___y_3269_ == 0)
{
uint32_t v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = 95;
v___x_3271_ = lean_uint32_dec_eq(v_c_3267_, v___x_3270_);
if (v___x_3271_ == 0)
{
uint32_t v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = 46;
v___x_3273_ = lean_uint32_dec_eq(v_c_3267_, v___x_3272_);
if (v___x_3273_ == 0)
{
uint32_t v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = 101;
v___x_3275_ = lean_uint32_dec_eq(v_c_3267_, v___x_3274_);
if (v___x_3275_ == 0)
{
uint32_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = 69;
v___x_3277_ = lean_uint32_dec_eq(v_c_3267_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_dec(v_val_3261_);
lean_dec(v_i_3260_);
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
else
{
goto v___jp_3262_;
}
}
else
{
goto v___jp_3262_;
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_string_utf8_next(v_s_3259_, v_i_3260_);
lean_dec(v_i_3260_);
v___x_3280_ = lean_unsigned_to_nat(0u);
v___x_3281_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3259_, v___x_3279_, v_val_3261_, v___x_3280_);
return v___x_3281_;
}
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_string_utf8_next(v_s_3259_, v_i_3260_);
lean_dec(v_i_3260_);
v_i_3260_ = v___x_3282_;
goto _start;
}
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3284_ = lean_string_utf8_next(v_s_3259_, v_i_3260_);
lean_dec(v_i_3260_);
v___x_3285_ = lean_unsigned_to_nat(10u);
v___x_3286_ = lean_nat_mul(v___x_3285_, v_val_3261_);
lean_dec(v_val_3261_);
v___x_3287_ = lean_uint32_to_nat(v_c_3267_);
v___x_3288_ = lean_nat_add(v___x_3286_, v___x_3287_);
lean_dec(v___x_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_unsigned_to_nat(48u);
v___x_3290_ = lean_nat_sub(v___x_3288_, v___x_3289_);
lean_dec(v___x_3288_);
v_i_3260_ = v___x_3284_;
v_val_3261_ = v___x_3290_;
goto _start;
}
}
}
else
{
lean_object* v___x_3296_; 
lean_dec(v_val_3261_);
lean_dec(v_i_3260_);
v___x_3296_ = lean_box(0);
return v___x_3296_;
}
v___jp_3262_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_string_utf8_next(v_s_3259_, v_i_3260_);
lean_dec(v_i_3260_);
v___x_3264_ = lean_unsigned_to_nat(0u);
v___x_3265_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3259_, v___x_3263_, v_val_3261_, v___x_3264_);
return v___x_3265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3297_, lean_object* v_i_3298_, lean_object* v_val_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3297_, v_i_3298_, v_val_3299_);
lean_dec_ref(v_s_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3301_){
_start:
{
lean_object* v_len_3302_; lean_object* v___x_3303_; uint8_t v___y_3305_; uint8_t v___x_3308_; 
v_len_3302_ = lean_string_length(v_s_3301_);
v___x_3303_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_nat_dec_eq(v_len_3302_, v___x_3303_);
lean_dec(v_len_3302_);
if (v___x_3308_ == 0)
{
uint32_t v_c_3309_; uint32_t v___x_3310_; uint8_t v___x_3311_; 
v_c_3309_ = lean_string_utf8_get(v_s_3301_, v___x_3303_);
v___x_3310_ = 48;
v___x_3311_ = lean_uint32_dec_le(v___x_3310_, v_c_3309_);
if (v___x_3311_ == 0)
{
v___y_3305_ = v___x_3311_;
goto v___jp_3304_;
}
else
{
uint32_t v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = 57;
v___x_3313_ = lean_uint32_dec_le(v_c_3309_, v___x_3312_);
v___y_3305_ = v___x_3313_;
goto v___jp_3304_;
}
}
else
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_box(0);
return v___x_3314_;
}
v___jp_3304_:
{
if (v___y_3305_ == 0)
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_box(0);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3301_, v___x_3303_, v___x_3303_);
return v___x_3307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3315_);
lean_dec_ref(v_s_3315_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3317_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3319_ = l_Lean_Syntax_isLit_x3f(v___x_3318_, v_stx_3317_);
if (lean_obj_tag(v___x_3319_) == 1)
{
lean_object* v_val_3320_; lean_object* v___x_3321_; 
v_val_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_val_3320_);
lean_dec_ref(v___x_3319_);
v___x_3321_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3320_);
lean_dec(v_val_3320_);
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; 
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
return v___x_3322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3323_);
lean_dec(v_stx_3323_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3325_){
_start:
{
switch(lean_obj_tag(v_x_3325_))
{
case 2:
{
lean_object* v_val_3326_; lean_object* v___x_3327_; 
v_val_3326_ = lean_ctor_get(v_x_3325_, 1);
lean_inc_ref(v_val_3326_);
lean_dec_ref(v_x_3325_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_val_3326_);
return v___x_3327_;
}
case 3:
{
lean_object* v_rawVal_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_rawVal_3328_ = lean_ctor_get(v_x_3325_, 1);
lean_inc_ref(v_rawVal_3328_);
lean_dec_ref(v_x_3325_);
v___x_3329_ = lean_substring_tostring(v_rawVal_3328_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
}
default: 
{
lean_object* v___x_3331_; 
lean_dec(v_x_3325_);
v___x_3331_ = lean_box(0);
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_unsigned_to_nat(0u);
return v___x_3334_;
}
else
{
lean_object* v_val_3335_; 
v_val_3335_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_val_3335_);
lean_dec_ref(v___x_3333_);
return v_val_3335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Syntax_toNat(v_stx_3336_);
lean_dec(v_stx_3336_);
return v_res_3337_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = 9;
v___x_3339_ = lean_box_uint32(v___x_3338_);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = 10;
v___x_3341_ = lean_box_uint32(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = 13;
v___x_3343_ = lean_box_uint32(v___x_3342_);
return v___x_3343_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = 39;
v___x_3345_ = lean_box_uint32(v___x_3344_);
return v___x_3345_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = 34;
v___x_3347_ = lean_box_uint32(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = 92;
v___x_3349_ = lean_box_uint32(v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3350_, lean_object* v_i_3351_){
_start:
{
uint32_t v_c_3352_; lean_object* v_i_3353_; uint32_t v___x_3354_; uint8_t v___x_3355_; 
v_c_3352_ = lean_string_utf8_get(v_s_3350_, v_i_3351_);
v_i_3353_ = lean_string_utf8_next(v_s_3350_, v_i_3351_);
v___x_3354_ = 92;
v___x_3355_ = lean_uint32_dec_eq(v_c_3352_, v___x_3354_);
if (v___x_3355_ == 0)
{
uint32_t v___x_3356_; uint8_t v___x_3357_; 
v___x_3356_ = 34;
v___x_3357_ = lean_uint32_dec_eq(v_c_3352_, v___x_3356_);
if (v___x_3357_ == 0)
{
uint32_t v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = 39;
v___x_3359_ = lean_uint32_dec_eq(v_c_3352_, v___x_3358_);
if (v___x_3359_ == 0)
{
uint32_t v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = 114;
v___x_3361_ = lean_uint32_dec_eq(v_c_3352_, v___x_3360_);
if (v___x_3361_ == 0)
{
uint32_t v___x_3362_; uint8_t v___x_3363_; 
v___x_3362_ = 110;
v___x_3363_ = lean_uint32_dec_eq(v_c_3352_, v___x_3362_);
if (v___x_3363_ == 0)
{
uint32_t v___x_3364_; uint8_t v___x_3365_; 
v___x_3364_ = 116;
v___x_3365_ = lean_uint32_dec_eq(v_c_3352_, v___x_3364_);
if (v___x_3365_ == 0)
{
uint32_t v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = 120;
v___x_3367_ = lean_uint32_dec_eq(v_c_3352_, v___x_3366_);
if (v___x_3367_ == 0)
{
uint32_t v___x_3368_; uint8_t v___x_3369_; 
v___x_3368_ = 117;
v___x_3369_ = lean_uint32_dec_eq(v_c_3352_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_dec(v_i_3353_);
v___x_3370_ = lean_box(0);
return v___x_3370_;
}
else
{
lean_object* v___x_3371_; 
v___x_3371_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3350_, v_i_3353_);
lean_dec(v_i_3353_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_box(0);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v_fst_3374_; lean_object* v_snd_3375_; lean_object* v___x_3376_; 
v_val_3373_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_val_3373_);
lean_dec_ref(v___x_3371_);
v_fst_3374_ = lean_ctor_get(v_val_3373_, 0);
lean_inc(v_fst_3374_);
v_snd_3375_ = lean_ctor_get(v_val_3373_, 1);
lean_inc(v_snd_3375_);
lean_dec(v_val_3373_);
v___x_3376_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3350_, v_snd_3375_);
lean_dec(v_snd_3375_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; 
lean_dec(v_fst_3374_);
v___x_3377_ = lean_box(0);
return v___x_3377_;
}
else
{
lean_object* v_val_3378_; lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3381_; 
v_val_3378_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_val_3378_);
lean_dec_ref(v___x_3376_);
v_fst_3379_ = lean_ctor_get(v_val_3378_, 0);
lean_inc(v_fst_3379_);
v_snd_3380_ = lean_ctor_get(v_val_3378_, 1);
lean_inc(v_snd_3380_);
lean_dec(v_val_3378_);
v___x_3381_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3350_, v_snd_3380_);
lean_dec(v_snd_3380_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v___x_3382_; 
lean_dec(v_fst_3379_);
lean_dec(v_fst_3374_);
v___x_3382_ = lean_box(0);
return v___x_3382_;
}
else
{
lean_object* v_val_3383_; lean_object* v_fst_3384_; lean_object* v_snd_3385_; lean_object* v___x_3386_; 
v_val_3383_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_val_3383_);
lean_dec_ref(v___x_3381_);
v_fst_3384_ = lean_ctor_get(v_val_3383_, 0);
lean_inc(v_fst_3384_);
v_snd_3385_ = lean_ctor_get(v_val_3383_, 1);
lean_inc(v_snd_3385_);
lean_dec(v_val_3383_);
v___x_3386_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3350_, v_snd_3385_);
lean_dec(v_snd_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3387_; 
lean_dec(v_fst_3384_);
lean_dec(v_fst_3379_);
lean_dec(v_fst_3374_);
v___x_3387_ = lean_box(0);
return v___x_3387_;
}
else
{
lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3413_; 
v_val_3388_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3390_ = v___x_3386_;
v_isShared_3391_ = v_isSharedCheck_3413_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_dec(v___x_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3413_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3412_; 
v_fst_3392_ = lean_ctor_get(v_val_3388_, 0);
v_snd_3393_ = lean_ctor_get(v_val_3388_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_val_3388_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3395_ = v_val_3388_;
v_isShared_3396_ = v_isSharedCheck_3412_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_snd_3393_);
lean_inc(v_fst_3392_);
lean_dec(v_val_3388_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3412_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint32_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3397_ = lean_unsigned_to_nat(16u);
v___x_3398_ = lean_nat_mul(v___x_3397_, v_fst_3374_);
lean_dec(v_fst_3374_);
v___x_3399_ = lean_nat_add(v___x_3398_, v_fst_3379_);
lean_dec(v_fst_3379_);
lean_dec(v___x_3398_);
v___x_3400_ = lean_nat_mul(v___x_3397_, v___x_3399_);
lean_dec(v___x_3399_);
v___x_3401_ = lean_nat_add(v___x_3400_, v_fst_3384_);
lean_dec(v_fst_3384_);
lean_dec(v___x_3400_);
v___x_3402_ = lean_nat_mul(v___x_3397_, v___x_3401_);
lean_dec(v___x_3401_);
v___x_3403_ = lean_nat_add(v___x_3402_, v_fst_3392_);
lean_dec(v_fst_3392_);
lean_dec(v___x_3402_);
v___x_3404_ = l_Char_ofNat(v___x_3403_);
lean_dec(v___x_3403_);
v___x_3405_ = lean_box_uint32(v___x_3404_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3405_);
v___x_3407_ = v___x_3395_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_snd_3393_);
v___x_3407_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3409_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3407_);
v___x_3409_ = v___x_3390_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
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
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3350_, v_i_3353_);
lean_dec(v_i_3353_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_box(0);
return v___x_3415_;
}
else
{
lean_object* v_val_3416_; lean_object* v_fst_3417_; lean_object* v_snd_3418_; lean_object* v___x_3419_; 
v_val_3416_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_val_3416_);
lean_dec_ref(v___x_3414_);
v_fst_3417_ = lean_ctor_get(v_val_3416_, 0);
lean_inc(v_fst_3417_);
v_snd_3418_ = lean_ctor_get(v_val_3416_, 1);
lean_inc(v_snd_3418_);
lean_dec(v_val_3416_);
v___x_3419_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3350_, v_snd_3418_);
lean_dec(v_snd_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; 
lean_dec(v_fst_3417_);
v___x_3420_ = lean_box(0);
return v___x_3420_;
}
else
{
lean_object* v_val_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3442_; 
v_val_3421_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3423_ = v___x_3419_;
v_isShared_3424_ = v_isSharedCheck_3442_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_val_3421_);
lean_dec(v___x_3419_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3442_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_fst_3425_; lean_object* v_snd_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3441_; 
v_fst_3425_ = lean_ctor_get(v_val_3421_, 0);
v_snd_3426_ = lean_ctor_get(v_val_3421_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_val_3421_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3428_ = v_val_3421_;
v_isShared_3429_ = v_isSharedCheck_3441_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_snd_3426_);
lean_inc(v_fst_3425_);
lean_dec(v_val_3421_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3441_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint32_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3430_ = lean_unsigned_to_nat(16u);
v___x_3431_ = lean_nat_mul(v___x_3430_, v_fst_3417_);
lean_dec(v_fst_3417_);
v___x_3432_ = lean_nat_add(v___x_3431_, v_fst_3425_);
lean_dec(v_fst_3425_);
lean_dec(v___x_3431_);
v___x_3433_ = l_Char_ofNat(v___x_3432_);
lean_dec(v___x_3432_);
v___x_3434_ = lean_box_uint32(v___x_3433_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3434_);
v___x_3436_ = v___x_3428_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_snd_3426_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3436_);
v___x_3438_ = v___x_3423_;
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
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v_i_3353_);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v_i_3353_);
v___x_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v_i_3353_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v_i_3353_);
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
return v___x_3454_;
}
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
lean_ctor_set(v___x_3456_, 1, v_i_3353_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_i_3353_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3461_, lean_object* v_i_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Syntax_decodeQuotedChar(v_s_3461_, v_i_3462_);
lean_dec(v_i_3462_);
lean_dec_ref(v_s_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3464_){
_start:
{
uint8_t v___y_3466_; uint32_t v___x_3471_; uint8_t v___x_3472_; 
v___x_3471_ = 32;
v___x_3472_ = lean_uint32_dec_eq(v___y_3464_, v___x_3471_);
if (v___x_3472_ == 0)
{
uint32_t v___x_3473_; uint8_t v___x_3474_; 
v___x_3473_ = 9;
v___x_3474_ = lean_uint32_dec_eq(v___y_3464_, v___x_3473_);
v___y_3466_ = v___x_3474_;
goto v___jp_3465_;
}
else
{
v___y_3466_ = v___x_3472_;
goto v___jp_3465_;
}
v___jp_3465_:
{
if (v___y_3466_ == 0)
{
uint32_t v___x_3467_; uint8_t v___x_3468_; 
v___x_3467_ = 13;
v___x_3468_ = lean_uint32_dec_eq(v___y_3464_, v___x_3467_);
if (v___x_3468_ == 0)
{
uint32_t v___x_3469_; uint8_t v___x_3470_; 
v___x_3469_ = 10;
v___x_3470_ = lean_uint32_dec_eq(v___y_3464_, v___x_3469_);
return v___x_3470_;
}
else
{
return v___x_3468_;
}
}
else
{
return v___y_3466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3475_){
_start:
{
uint32_t v___y_233__boxed_3476_; uint8_t v_res_3477_; lean_object* v_r_3478_; 
v___y_233__boxed_3476_ = lean_unbox_uint32(v___y_3475_);
lean_dec(v___y_3475_);
v_res_3477_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_233__boxed_3476_);
v_r_3478_ = lean_box(v_res_3477_);
return v_r_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3480_, lean_object* v_i_3481_){
_start:
{
lean_object* v___f_3482_; uint8_t v___y_3488_; uint32_t v___x_3490_; uint8_t v___y_3492_; uint32_t v___x_3497_; uint8_t v___x_3498_; 
v___f_3482_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3490_ = lean_string_utf8_get(v_s_3480_, v_i_3481_);
v___x_3497_ = 32;
v___x_3498_ = lean_uint32_dec_eq(v___x_3490_, v___x_3497_);
if (v___x_3498_ == 0)
{
uint32_t v___x_3499_; uint8_t v___x_3500_; 
v___x_3499_ = 9;
v___x_3500_ = lean_uint32_dec_eq(v___x_3490_, v___x_3499_);
v___y_3492_ = v___x_3500_;
goto v___jp_3491_;
}
else
{
v___y_3492_ = v___x_3498_;
goto v___jp_3491_;
}
v___jp_3483_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = lean_string_utf8_next(v_s_3480_, v_i_3481_);
v___x_3485_ = lean_string_nextwhile(v_s_3480_, v___f_3482_, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
v___jp_3487_:
{
if (v___y_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref(v_s_3480_);
v___x_3489_ = lean_box(0);
return v___x_3489_;
}
else
{
goto v___jp_3483_;
}
}
v___jp_3491_:
{
if (v___y_3492_ == 0)
{
uint32_t v___x_3493_; uint8_t v___x_3494_; 
v___x_3493_ = 13;
v___x_3494_ = lean_uint32_dec_eq(v___x_3490_, v___x_3493_);
if (v___x_3494_ == 0)
{
uint32_t v___x_3495_; uint8_t v___x_3496_; 
v___x_3495_ = 10;
v___x_3496_ = lean_uint32_dec_eq(v___x_3490_, v___x_3495_);
v___y_3488_ = v___x_3496_;
goto v___jp_3487_;
}
else
{
v___y_3488_ = v___x_3494_;
goto v___jp_3487_;
}
}
else
{
goto v___jp_3483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3501_, lean_object* v_i_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Syntax_decodeStringGap(v_s_3501_, v_i_3502_);
lean_dec(v_i_3502_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3504_, lean_object* v_i_3505_, lean_object* v_acc_3506_){
_start:
{
uint32_t v_c_3507_; uint32_t v___x_3508_; uint8_t v___x_3509_; 
v_c_3507_ = lean_string_utf8_get(v_s_3504_, v_i_3505_);
v___x_3508_ = 34;
v___x_3509_ = lean_uint32_dec_eq(v_c_3507_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v_i_3510_; uint8_t v___x_3511_; 
v_i_3510_ = lean_string_utf8_next(v_s_3504_, v_i_3505_);
lean_dec(v_i_3505_);
v___x_3511_ = lean_string_utf8_at_end(v_s_3504_, v_i_3510_);
if (v___x_3511_ == 0)
{
uint32_t v___x_3512_; uint8_t v___x_3513_; 
v___x_3512_ = 92;
v___x_3513_ = lean_uint32_dec_eq(v_c_3507_, v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_string_push(v_acc_3506_, v_c_3507_);
v_i_3505_ = v_i_3510_;
v_acc_3506_ = v___x_3514_;
goto _start;
}
else
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Syntax_decodeQuotedChar(v_s_3504_, v_i_3510_);
if (lean_obj_tag(v___x_3516_) == 1)
{
lean_object* v_val_3517_; lean_object* v_fst_3518_; lean_object* v_snd_3519_; uint32_t v___x_3520_; lean_object* v___x_3521_; 
lean_dec(v_i_3510_);
v_val_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_val_3517_);
lean_dec_ref(v___x_3516_);
v_fst_3518_ = lean_ctor_get(v_val_3517_, 0);
lean_inc(v_fst_3518_);
v_snd_3519_ = lean_ctor_get(v_val_3517_, 1);
lean_inc(v_snd_3519_);
lean_dec(v_val_3517_);
v___x_3520_ = lean_unbox_uint32(v_fst_3518_);
lean_dec(v_fst_3518_);
v___x_3521_ = lean_string_push(v_acc_3506_, v___x_3520_);
v_i_3505_ = v_snd_3519_;
v_acc_3506_ = v___x_3521_;
goto _start;
}
else
{
lean_object* v___x_3523_; 
lean_dec(v___x_3516_);
lean_inc_ref(v_s_3504_);
v___x_3523_ = l_Lean_Syntax_decodeStringGap(v_s_3504_, v_i_3510_);
lean_dec(v_i_3510_);
if (lean_obj_tag(v___x_3523_) == 1)
{
lean_object* v_val_3524_; 
v_val_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_val_3524_);
lean_dec_ref(v___x_3523_);
v_i_3505_ = v_val_3524_;
goto _start;
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3523_);
lean_dec_ref(v_acc_3506_);
lean_dec_ref(v_s_3504_);
v___x_3526_ = lean_box(0);
return v___x_3526_;
}
}
}
}
else
{
lean_object* v___x_3527_; 
lean_dec(v_i_3510_);
lean_dec_ref(v_acc_3506_);
lean_dec_ref(v_s_3504_);
v___x_3527_ = lean_box(0);
return v___x_3527_;
}
}
else
{
lean_object* v___x_3528_; 
lean_dec(v_i_3505_);
lean_dec_ref(v_s_3504_);
v___x_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3528_, 0, v_acc_3506_);
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3529_, lean_object* v_i_3530_, lean_object* v_num_3531_){
_start:
{
uint32_t v_c_3532_; lean_object* v_i_3533_; uint32_t v___x_3534_; uint8_t v___x_3535_; 
v_c_3532_ = lean_string_utf8_get(v_s_3529_, v_i_3530_);
v_i_3533_ = lean_string_utf8_next(v_s_3529_, v_i_3530_);
lean_dec(v_i_3530_);
v___x_3534_ = 35;
v___x_3535_ = lean_uint32_dec_eq(v_c_3532_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3536_ = lean_string_utf8_byte_size(v_s_3529_);
v___x_3537_ = lean_unsigned_to_nat(1u);
v___x_3538_ = lean_nat_add(v_num_3531_, v___x_3537_);
lean_dec(v_num_3531_);
v___x_3539_ = lean_nat_sub(v___x_3536_, v___x_3538_);
lean_dec(v___x_3538_);
v___x_3540_ = lean_string_utf8_extract(v_s_3529_, v_i_3533_, v___x_3539_);
lean_dec(v___x_3539_);
lean_dec(v_i_3533_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = lean_nat_add(v_num_3531_, v___x_3541_);
lean_dec(v_num_3531_);
v_i_3530_ = v_i_3533_;
v_num_3531_ = v___x_3542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3544_, lean_object* v_i_3545_, lean_object* v_num_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3544_, v_i_3545_, v_num_3546_);
lean_dec_ref(v_s_3544_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3548_){
_start:
{
lean_object* v___x_3549_; uint32_t v___x_3550_; uint32_t v___x_3551_; uint8_t v___x_3552_; 
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = lean_string_utf8_get(v_s_3548_, v___x_3549_);
v___x_3551_ = 114;
v___x_3552_ = lean_uint32_dec_eq(v___x_3550_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3555_ = l_Lean_Syntax_decodeStrLitAux(v_s_3548_, v___x_3553_, v___x_3554_);
return v___x_3555_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = lean_unsigned_to_nat(1u);
v___x_3557_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3548_, v___x_3556_, v___x_3549_);
lean_dec_ref(v_s_3548_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3559_){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3561_ = l_Lean_Syntax_isLit_x3f(v___x_3560_, v_stx_3559_);
if (lean_obj_tag(v___x_3561_) == 1)
{
lean_object* v_val_3562_; lean_object* v___x_3563_; 
v_val_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_val_3562_);
lean_dec_ref(v___x_3561_);
v___x_3563_ = l_Lean_Syntax_decodeStrLit(v_val_3562_);
return v___x_3563_;
}
else
{
lean_object* v___x_3564_; 
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3565_);
lean_dec(v_stx_3565_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3567_){
_start:
{
lean_object* v___x_3568_; uint32_t v_c_3569_; uint32_t v___x_3570_; uint8_t v___x_3571_; 
v___x_3568_ = lean_unsigned_to_nat(1u);
v_c_3569_ = lean_string_utf8_get(v_s_3567_, v___x_3568_);
v___x_3570_ = 92;
v___x_3571_ = lean_uint32_dec_eq(v_c_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_box_uint32(v_c_3569_);
v___x_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = lean_unsigned_to_nat(2u);
v___x_3575_ = l_Lean_Syntax_decodeQuotedChar(v_s_3567_, v___x_3574_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_box(0);
return v___x_3576_;
}
else
{
lean_object* v_val_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3585_; 
v_val_3577_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3579_ = v___x_3575_;
v_isShared_3580_ = v_isSharedCheck_3585_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_val_3577_);
lean_dec(v___x_3575_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3585_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_fst_3581_; lean_object* v___x_3583_; 
v_fst_3581_ = lean_ctor_get(v_val_3577_, 0);
lean_inc(v_fst_3581_);
lean_dec(v_val_3577_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v_fst_3581_);
v___x_3583_ = v___x_3579_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_fst_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Syntax_decodeCharLit(v_s_3586_);
lean_dec_ref(v_s_3586_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3588_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3590_ = l_Lean_Syntax_isLit_x3f(v___x_3589_, v_stx_3588_);
if (lean_obj_tag(v___x_3590_) == 1)
{
lean_object* v_val_3591_; lean_object* v___x_3592_; 
v_val_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_val_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = l_Lean_Syntax_decodeCharLit(v_val_3591_);
lean_dec(v_val_3591_);
return v___x_3592_;
}
else
{
lean_object* v___x_3593_; 
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3594_);
lean_dec(v_stx_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3596_){
_start:
{
uint8_t v___y_3598_; uint8_t v___y_3610_; uint32_t v___x_3620_; uint8_t v___x_3621_; 
v___x_3620_ = 65;
v___x_3621_ = lean_uint32_dec_le(v___x_3620_, v___y_3596_);
if (v___x_3621_ == 0)
{
goto v___jp_3615_;
}
else
{
uint32_t v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = 90;
v___x_3623_ = lean_uint32_dec_le(v___y_3596_, v___x_3622_);
if (v___x_3623_ == 0)
{
goto v___jp_3615_;
}
else
{
return v___x_3623_;
}
}
v___jp_3597_:
{
if (v___y_3598_ == 0)
{
uint32_t v___x_3599_; uint8_t v___x_3600_; 
v___x_3599_ = 95;
v___x_3600_ = lean_uint32_dec_eq(v___y_3596_, v___x_3599_);
if (v___x_3600_ == 0)
{
uint32_t v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = 39;
v___x_3602_ = lean_uint32_dec_eq(v___y_3596_, v___x_3601_);
if (v___x_3602_ == 0)
{
uint32_t v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = 33;
v___x_3604_ = lean_uint32_dec_eq(v___y_3596_, v___x_3603_);
if (v___x_3604_ == 0)
{
uint32_t v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = 63;
v___x_3606_ = lean_uint32_dec_eq(v___y_3596_, v___x_3605_);
if (v___x_3606_ == 0)
{
uint8_t v___x_3607_; 
v___x_3607_ = l_Lean_isLetterLike(v___y_3596_);
if (v___x_3607_ == 0)
{
uint8_t v___x_3608_; 
v___x_3608_ = l_Lean_isSubScriptAlnum(v___y_3596_);
return v___x_3608_;
}
else
{
return v___x_3607_;
}
}
else
{
return v___x_3606_;
}
}
else
{
return v___x_3604_;
}
}
else
{
return v___x_3602_;
}
}
else
{
return v___x_3600_;
}
}
else
{
return v___y_3598_;
}
}
v___jp_3609_:
{
if (v___y_3610_ == 0)
{
uint32_t v___x_3611_; uint8_t v___x_3612_; 
v___x_3611_ = 48;
v___x_3612_ = lean_uint32_dec_le(v___x_3611_, v___y_3596_);
if (v___x_3612_ == 0)
{
v___y_3598_ = v___x_3612_;
goto v___jp_3597_;
}
else
{
uint32_t v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = 57;
v___x_3614_ = lean_uint32_dec_le(v___y_3596_, v___x_3613_);
v___y_3598_ = v___x_3614_;
goto v___jp_3597_;
}
}
else
{
return v___y_3610_;
}
}
v___jp_3615_:
{
uint32_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = 97;
v___x_3617_ = lean_uint32_dec_le(v___x_3616_, v___y_3596_);
if (v___x_3617_ == 0)
{
v___y_3610_ = v___x_3617_;
goto v___jp_3609_;
}
else
{
uint32_t v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = 122;
v___x_3619_ = lean_uint32_dec_le(v___y_3596_, v___x_3618_);
v___y_3610_ = v___x_3619_;
goto v___jp_3609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3624_){
_start:
{
uint32_t v___y_1135__boxed_3625_; uint8_t v_res_3626_; lean_object* v_r_3627_; 
v___y_1135__boxed_3625_ = lean_unbox_uint32(v___y_3624_);
lean_dec(v___y_3624_);
v_res_3626_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_1135__boxed_3625_);
v_r_3627_ = lean_box(v_res_3626_);
return v_r_3627_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___y_3628_){
_start:
{
uint32_t v___x_3629_; uint8_t v___x_3630_; 
v___x_3629_ = 48;
v___x_3630_ = lean_uint32_dec_le(v___x_3629_, v___y_3628_);
if (v___x_3630_ == 0)
{
return v___x_3630_;
}
else
{
uint32_t v___x_3631_; uint8_t v___x_3632_; 
v___x_3631_ = 57;
v___x_3632_ = lean_uint32_dec_le(v___y_3628_, v___x_3631_);
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___y_3633_){
_start:
{
uint32_t v___y_1192__boxed_3634_; uint8_t v_res_3635_; lean_object* v_r_3636_; 
v___y_1192__boxed_3634_ = lean_unbox_uint32(v___y_3633_);
lean_dec(v___y_3633_);
v_res_3635_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___y_1192__boxed_3634_);
v_r_3636_ = lean_box(v_res_3635_);
return v_r_3636_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3637_, uint8_t v___x_3638_, uint32_t v_x_3639_){
_start:
{
uint32_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = 187;
v___x_3641_ = lean_uint32_dec_eq(v_x_3639_, v___x_3640_);
if (v___x_3641_ == 0)
{
return v___x_3637_;
}
else
{
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3642_, lean_object* v___x_3643_, lean_object* v_x_3644_){
_start:
{
uint8_t v___x_1203__boxed_3645_; uint8_t v___x_1204__boxed_3646_; uint32_t v_x_1205__boxed_3647_; uint8_t v_res_3648_; lean_object* v_r_3649_; 
v___x_1203__boxed_3645_ = lean_unbox(v___x_3642_);
v___x_1204__boxed_3646_ = lean_unbox(v___x_3643_);
v_x_1205__boxed_3647_ = lean_unbox_uint32(v_x_3644_);
lean_dec(v_x_3644_);
v_res_3648_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_1203__boxed_3645_, v___x_1204__boxed_3646_, v_x_1205__boxed_3647_);
v_r_3649_ = lean_box(v_res_3648_);
return v_r_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3652_, lean_object* v_acc_3653_){
_start:
{
lean_object* v_ss_3655_; lean_object* v_acc_3656_; uint8_t v___x_3665_; 
lean_inc_ref(v_ss_3652_);
v___x_3665_ = lean_substring_isempty(v_ss_3652_);
if (v___x_3665_ == 0)
{
uint32_t v_curr_3666_; uint32_t v___x_3667_; uint8_t v___x_3668_; 
lean_inc_ref(v_ss_3652_);
v_curr_3666_ = lean_substring_front(v_ss_3652_);
v___x_3667_ = 171;
v___x_3668_ = lean_uint32_dec_eq(v_curr_3666_, v___x_3667_);
if (v___x_3668_ == 0)
{
lean_object* v___f_3669_; lean_object* v___f_3680_; uint8_t v___y_3682_; uint8_t v___y_3694_; uint8_t v___y_3700_; uint32_t v___x_3709_; uint8_t v___x_3710_; 
v___f_3669_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___f_3680_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1));
v___x_3709_ = 65;
v___x_3710_ = lean_uint32_dec_le(v___x_3709_, v_curr_3666_);
if (v___x_3710_ == 0)
{
goto v___jp_3704_;
}
else
{
uint32_t v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = 90;
v___x_3712_ = lean_uint32_dec_le(v_curr_3666_, v___x_3711_);
if (v___x_3712_ == 0)
{
goto v___jp_3704_;
}
else
{
goto v___jp_3670_;
}
}
v___jp_3670_:
{
lean_object* v_idPart_3671_; lean_object* v_startPos_3672_; lean_object* v_stopPos_3673_; lean_object* v_startPos_3674_; lean_object* v_stopPos_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_inc_ref(v_ss_3652_);
v_idPart_3671_ = lean_substring_takewhile(v_ss_3652_, v___f_3669_);
v_startPos_3672_ = lean_ctor_get(v_idPart_3671_, 1);
lean_inc(v_startPos_3672_);
v_stopPos_3673_ = lean_ctor_get(v_idPart_3671_, 2);
lean_inc(v_stopPos_3673_);
v_startPos_3674_ = lean_ctor_get(v_ss_3652_, 1);
v_stopPos_3675_ = lean_ctor_get(v_ss_3652_, 2);
v___x_3676_ = lean_nat_sub(v_stopPos_3673_, v_startPos_3672_);
lean_dec(v_startPos_3672_);
lean_dec(v_stopPos_3673_);
v___x_3677_ = lean_nat_sub(v_stopPos_3675_, v_startPos_3674_);
v___x_3678_ = lean_substring_extract(v_ss_3652_, v___x_3676_, v___x_3677_);
v___x_3679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_idPart_3671_);
lean_ctor_set(v___x_3679_, 1, v_acc_3653_);
v_ss_3655_ = v___x_3678_;
v_acc_3656_ = v___x_3679_;
goto v___jp_3654_;
}
v___jp_3681_:
{
if (v___y_3682_ == 0)
{
lean_object* v___x_3683_; 
lean_dec(v_acc_3653_);
lean_dec_ref(v_ss_3652_);
v___x_3683_ = lean_box(0);
return v___x_3683_;
}
else
{
lean_object* v_idPart_3684_; lean_object* v_startPos_3685_; lean_object* v_stopPos_3686_; lean_object* v_startPos_3687_; lean_object* v_stopPos_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
lean_inc_ref(v_ss_3652_);
v_idPart_3684_ = lean_substring_takewhile(v_ss_3652_, v___f_3680_);
v_startPos_3685_ = lean_ctor_get(v_idPart_3684_, 1);
lean_inc(v_startPos_3685_);
v_stopPos_3686_ = lean_ctor_get(v_idPart_3684_, 2);
lean_inc(v_stopPos_3686_);
v_startPos_3687_ = lean_ctor_get(v_ss_3652_, 1);
v_stopPos_3688_ = lean_ctor_get(v_ss_3652_, 2);
v___x_3689_ = lean_nat_sub(v_stopPos_3686_, v_startPos_3685_);
lean_dec(v_startPos_3685_);
lean_dec(v_stopPos_3686_);
v___x_3690_ = lean_nat_sub(v_stopPos_3688_, v_startPos_3687_);
v___x_3691_ = lean_substring_extract(v_ss_3652_, v___x_3689_, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_idPart_3684_);
lean_ctor_set(v___x_3692_, 1, v_acc_3653_);
v_ss_3655_ = v___x_3691_;
v_acc_3656_ = v___x_3692_;
goto v___jp_3654_;
}
}
v___jp_3693_:
{
if (v___y_3694_ == 0)
{
uint32_t v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = 48;
v___x_3696_ = lean_uint32_dec_le(v___x_3695_, v_curr_3666_);
if (v___x_3696_ == 0)
{
v___y_3682_ = v___x_3696_;
goto v___jp_3681_;
}
else
{
uint32_t v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = 57;
v___x_3698_ = lean_uint32_dec_le(v_curr_3666_, v___x_3697_);
v___y_3682_ = v___x_3698_;
goto v___jp_3681_;
}
}
else
{
goto v___jp_3670_;
}
}
v___jp_3699_:
{
if (v___y_3700_ == 0)
{
uint32_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = 95;
v___x_3702_ = lean_uint32_dec_eq(v_curr_3666_, v___x_3701_);
if (v___x_3702_ == 0)
{
uint8_t v___x_3703_; 
v___x_3703_ = l_Lean_isLetterLike(v_curr_3666_);
v___y_3694_ = v___x_3703_;
goto v___jp_3693_;
}
else
{
v___y_3694_ = v___x_3702_;
goto v___jp_3693_;
}
}
else
{
goto v___jp_3670_;
}
}
v___jp_3704_:
{
uint32_t v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = 97;
v___x_3706_ = lean_uint32_dec_le(v___x_3705_, v_curr_3666_);
if (v___x_3706_ == 0)
{
v___y_3700_ = v___x_3706_;
goto v___jp_3699_;
}
else
{
uint32_t v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = 122;
v___x_3708_ = lean_uint32_dec_le(v_curr_3666_, v___x_3707_);
v___y_3700_ = v___x_3708_;
goto v___jp_3699_;
}
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___f_3715_; lean_object* v_escapedPart_3716_; lean_object* v_str_3717_; lean_object* v_startPos_3718_; lean_object* v_stopPos_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3741_; 
v___x_3713_ = lean_box(v___x_3668_);
v___x_3714_ = lean_box(v___x_3665_);
v___f_3715_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3715_, 0, v___x_3713_);
lean_closure_set(v___f_3715_, 1, v___x_3714_);
lean_inc_ref(v_ss_3652_);
v_escapedPart_3716_ = lean_substring_takewhile(v_ss_3652_, v___f_3715_);
v_str_3717_ = lean_ctor_get(v_escapedPart_3716_, 0);
v_startPos_3718_ = lean_ctor_get(v_escapedPart_3716_, 1);
v_stopPos_3719_ = lean_ctor_get(v_escapedPart_3716_, 2);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_escapedPart_3716_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3721_ = v_escapedPart_3716_;
v_isShared_3722_ = v_isSharedCheck_3741_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_stopPos_3719_);
lean_inc(v_startPos_3718_);
lean_inc(v_str_3717_);
lean_dec(v_escapedPart_3716_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3741_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v_startPos_3723_; lean_object* v_stopPos_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v_escapedPart_3728_; 
v_startPos_3723_ = lean_ctor_get(v_ss_3652_, 1);
v_stopPos_3724_ = lean_ctor_get(v_ss_3652_, 2);
v___x_3725_ = lean_string_utf8_next(v_str_3717_, v_stopPos_3719_);
lean_dec(v_stopPos_3719_);
lean_inc(v_stopPos_3724_);
v___x_3726_ = lean_string_pos_min(v_stopPos_3724_, v___x_3725_);
lean_inc(v___x_3726_);
lean_inc(v_startPos_3718_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 2, v___x_3726_);
v_escapedPart_3728_ = v___x_3721_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_str_3717_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_startPos_3718_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v___x_3726_);
v_escapedPart_3728_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; uint8_t v___y_3731_; lean_object* v___x_3736_; uint32_t v___x_3737_; uint32_t v___x_3738_; uint8_t v___x_3739_; 
v___x_3729_ = lean_nat_sub(v___x_3726_, v_startPos_3718_);
lean_dec(v_startPos_3718_);
lean_dec(v___x_3726_);
lean_inc(v___x_3729_);
lean_inc_ref(v_escapedPart_3728_);
v___x_3736_ = lean_substring_prev(v_escapedPart_3728_, v___x_3729_);
lean_inc_ref(v_escapedPart_3728_);
v___x_3737_ = lean_substring_get(v_escapedPart_3728_, v___x_3736_);
v___x_3738_ = 187;
v___x_3739_ = lean_uint32_dec_eq(v___x_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
v___y_3731_ = v___x_3668_;
goto v___jp_3730_;
}
else
{
v___y_3731_ = v___x_3665_;
goto v___jp_3730_;
}
v___jp_3730_:
{
if (v___y_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = lean_nat_sub(v_stopPos_3724_, v_startPos_3723_);
v___x_3733_ = lean_substring_extract(v_ss_3652_, v___x_3729_, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_escapedPart_3728_);
lean_ctor_set(v___x_3734_, 1, v_acc_3653_);
v_ss_3655_ = v___x_3733_;
v_acc_3656_ = v___x_3734_;
goto v___jp_3654_;
}
else
{
lean_object* v___x_3735_; 
lean_dec(v___x_3729_);
lean_dec_ref(v_escapedPart_3728_);
lean_dec(v_acc_3653_);
lean_dec_ref(v_ss_3652_);
v___x_3735_ = lean_box(0);
return v___x_3735_;
}
}
}
}
}
}
else
{
lean_object* v___x_3742_; 
lean_dec(v_acc_3653_);
lean_dec_ref(v_ss_3652_);
v___x_3742_ = lean_box(0);
return v___x_3742_;
}
v___jp_3654_:
{
uint32_t v___x_3657_; uint32_t v___x_3658_; uint8_t v___x_3659_; 
lean_inc_ref(v_ss_3655_);
v___x_3657_ = lean_substring_front(v_ss_3655_);
v___x_3658_ = 46;
v___x_3659_ = lean_uint32_dec_eq(v___x_3657_, v___x_3658_);
if (v___x_3659_ == 0)
{
uint8_t v___x_3660_; 
v___x_3660_ = lean_substring_isempty(v_ss_3655_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec(v_acc_3656_);
v___x_3661_ = lean_box(0);
return v___x_3661_;
}
else
{
return v_acc_3656_;
}
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = lean_substring_drop(v_ss_3655_, v___x_3662_);
v_ss_3652_ = v___x_3663_;
v_acc_3653_ = v_acc_3656_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3743_){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3744_ = lean_box(0);
v___x_3745_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3743_, v___x_3744_);
v___x_3746_ = l_List_reverse___redArg(v___x_3745_);
return v___x_3746_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3750_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3751_ = lean_unsigned_to_nat(10u);
v___x_3752_ = lean_unsigned_to_nat(1230u);
v___x_3753_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3754_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3755_ = l_mkPanicMessageWithDecl(v___x_3754_, v___x_3753_, v___x_3752_, v___x_3751_, v___x_3750_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3756_, lean_object* v_x_3757_){
_start:
{
if (lean_obj_tag(v_x_3757_) == 0)
{
lean_inc(v_init_3756_);
return v_init_3756_;
}
else
{
lean_object* v_head_3758_; lean_object* v_tail_3759_; lean_object* v___x_3760_; lean_object* v_comp_3761_; uint8_t v___y_3763_; uint32_t v___x_3770_; uint32_t v___x_3771_; uint8_t v___x_3772_; 
v_head_3758_ = lean_ctor_get(v_x_3757_, 0);
lean_inc(v_head_3758_);
v_tail_3759_ = lean_ctor_get(v_x_3757_, 1);
lean_inc(v_tail_3759_);
lean_dec_ref(v_x_3757_);
v___x_3760_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3756_, v_tail_3759_);
v_comp_3761_ = lean_substring_tostring(v_head_3758_);
lean_inc_ref(v_comp_3761_);
v___x_3770_ = lean_string_front(v_comp_3761_);
v___x_3771_ = 171;
v___x_3772_ = lean_uint32_dec_eq(v___x_3770_, v___x_3771_);
if (v___x_3772_ == 0)
{
uint32_t v___x_3773_; uint8_t v___x_3774_; 
v___x_3773_ = 48;
v___x_3774_ = lean_uint32_dec_le(v___x_3773_, v___x_3770_);
if (v___x_3774_ == 0)
{
v___y_3763_ = v___x_3774_;
goto v___jp_3762_;
}
else
{
uint32_t v___x_3775_; uint8_t v___x_3776_; 
v___x_3775_ = 57;
v___x_3776_ = lean_uint32_dec_le(v___x_3770_, v___x_3775_);
v___y_3763_ = v___x_3776_;
goto v___jp_3762_;
}
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3777_ = lean_unsigned_to_nat(1u);
v___x_3778_ = lean_string_drop(v_comp_3761_, v___x_3777_);
v___x_3779_ = lean_string_dropright(v___x_3778_, v___x_3777_);
v___x_3780_ = l_Lean_Name_str___override(v___x_3760_, v___x_3779_);
return v___x_3780_;
}
v___jp_3762_:
{
if (v___y_3763_ == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Name_str___override(v___x_3760_, v_comp_3761_);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3761_);
lean_dec_ref(v_comp_3761_);
if (lean_obj_tag(v___x_3765_) == 1)
{
lean_object* v_val_3766_; lean_object* v___x_3767_; 
v_val_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_val_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = l_Lean_Name_num___override(v___x_3760_, v_val_3766_);
return v___x_3767_;
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_dec(v___x_3765_);
lean_dec(v___x_3760_);
v___x_3768_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3769_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3768_);
return v___x_3769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3781_, lean_object* v_x_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3781_, v_x_3782_);
lean_dec(v_init_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3784_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_box(0);
v___x_3786_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3784_, v___x_3785_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_box(0);
return v___x_3787_;
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_box(0);
v___x_3789_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3788_, v___x_3786_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3790_){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = lean_string_utf8_byte_size(v_s_3790_);
v___x_3793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3793_, 0, v_s_3790_);
lean_ctor_set(v___x_3793_, 1, v___x_3791_);
lean_ctor_set(v___x_3793_, 2, v___x_3792_);
v___x_3794_ = l_Substring_Raw_toName(v___x_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3795_){
_start:
{
lean_object* v___x_3796_; uint32_t v___x_3797_; uint32_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3796_ = lean_unsigned_to_nat(0u);
v___x_3797_ = lean_string_utf8_get(v_s_3795_, v___x_3796_);
v___x_3798_ = 96;
v___x_3799_ = lean_uint32_dec_eq(v___x_3797_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; 
lean_dec_ref(v_s_3795_);
v___x_3800_ = lean_box(0);
return v___x_3800_;
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3801_ = lean_string_utf8_byte_size(v_s_3795_);
v___x_3802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3802_, 0, v_s_3795_);
lean_ctor_set(v___x_3802_, 1, v___x_3796_);
lean_ctor_set(v___x_3802_, 2, v___x_3801_);
v___x_3803_ = lean_unsigned_to_nat(1u);
v___x_3804_ = lean_substring_drop(v___x_3802_, v___x_3803_);
v___x_3805_ = l_Substring_Raw_toName(v___x_3804_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_box(0);
return v___x_3806_;
}
else
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
return v___x_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3808_){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3810_ = l_Lean_Syntax_isLit_x3f(v___x_3809_, v_stx_3808_);
if (lean_obj_tag(v___x_3810_) == 1)
{
lean_object* v_val_3811_; lean_object* v___x_3812_; 
v_val_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_val_3811_);
lean_dec_ref(v___x_3810_);
v___x_3812_ = l_Lean_Syntax_decodeNameLit(v_val_3811_);
return v___x_3812_;
}
else
{
lean_object* v___x_3813_; 
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
return v___x_3813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3814_);
lean_dec(v_stx_3814_);
return v_res_3815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3816_){
_start:
{
if (lean_obj_tag(v_x_3816_) == 1)
{
lean_object* v_args_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
v_args_3817_ = lean_ctor_get(v_x_3816_, 2);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = lean_array_get_size(v_args_3817_);
v___x_3820_ = lean_nat_dec_lt(v___x_3818_, v___x_3819_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3822_){
_start:
{
uint8_t v_res_3823_; lean_object* v_r_3824_; 
v_res_3823_ = l_Lean_Syntax_hasArgs(v_x_3822_);
lean_dec(v_x_3822_);
v_r_3824_ = lean_box(v_res_3823_);
return v_r_3824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3825_){
_start:
{
if (lean_obj_tag(v_x_3825_) == 2)
{
uint8_t v___x_3826_; 
v___x_3826_ = 1;
return v___x_3826_;
}
else
{
uint8_t v___x_3827_; 
v___x_3827_ = 0;
return v___x_3827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3828_){
_start:
{
uint8_t v_res_3829_; lean_object* v_r_3830_; 
v_res_3829_ = l_Lean_Syntax_isAtom(v_x_3828_);
lean_dec(v_x_3828_);
v_r_3830_ = lean_box(v_res_3829_);
return v_r_3830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3831_, lean_object* v_x_3832_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 2)
{
lean_object* v_val_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_val_3833_ = lean_ctor_get(v_x_3832_, 1);
lean_inc_ref(v_val_3833_);
lean_dec_ref(v_x_3832_);
v___x_3834_ = lean_string_trim(v_val_3833_);
v___x_3835_ = lean_string_trim(v_token_3831_);
v___x_3836_ = lean_string_dec_eq(v___x_3834_, v___x_3835_);
lean_dec_ref(v___x_3835_);
lean_dec_ref(v___x_3834_);
return v___x_3836_;
}
else
{
uint8_t v___x_3837_; 
lean_dec(v_x_3832_);
lean_dec_ref(v_token_3831_);
v___x_3837_ = 0;
return v___x_3837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3838_, lean_object* v_x_3839_){
_start:
{
uint8_t v_res_3840_; lean_object* v_r_3841_; 
v_res_3840_ = l_Lean_Syntax_isToken(v_token_3838_, v_x_3839_);
v_r_3841_ = lean_box(v_res_3840_);
return v_r_3841_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3842_){
_start:
{
switch(lean_obj_tag(v_stx_3842_))
{
case 1:
{
lean_object* v_kind_3843_; lean_object* v_args_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_kind_3843_ = lean_ctor_get(v_stx_3842_, 1);
v_args_3844_ = lean_ctor_get(v_stx_3842_, 2);
v___x_3845_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3846_ = lean_name_eq(v_kind_3843_, v___x_3845_);
if (v___x_3846_ == 0)
{
return v___x_3846_;
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v___x_3847_ = lean_array_get_size(v_args_3844_);
v___x_3848_ = lean_unsigned_to_nat(0u);
v___x_3849_ = lean_nat_dec_eq(v___x_3847_, v___x_3848_);
return v___x_3849_;
}
}
case 0:
{
uint8_t v___x_3850_; 
v___x_3850_ = 1;
return v___x_3850_;
}
default: 
{
uint8_t v___x_3851_; 
v___x_3851_ = 0;
return v___x_3851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3852_){
_start:
{
uint8_t v_res_3853_; lean_object* v_r_3854_; 
v_res_3853_ = l_Lean_Syntax_isNone(v_stx_3852_);
lean_dec(v_stx_3852_);
v_r_3854_ = lean_box(v_res_3853_);
return v_r_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Lean_Syntax_getOptional_x3f(v_stx_3855_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_box(0);
return v___x_3857_;
}
else
{
lean_object* v_val_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3866_; 
v_val_3858_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3860_ = v___x_3856_;
v_isShared_3861_ = v_isSharedCheck_3866_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_val_3858_);
lean_dec(v___x_3856_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3866_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3862_ = l_Lean_Syntax_getId(v_val_3858_);
lean_dec(v_val_3858_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3862_);
v___x_3864_ = v___x_3860_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3867_);
lean_dec(v_stx_3867_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3869_, lean_object* v_x_3870_){
_start:
{
if (lean_obj_tag(v_x_3870_) == 1)
{
lean_object* v_args_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v_args_3871_ = lean_ctor_get(v_x_3870_, 2);
lean_inc_ref(v_p_3869_);
lean_inc_ref(v_x_3870_);
v___x_3872_ = lean_apply_1(v_p_3869_, v_x_3870_);
v___x_3873_ = lean_unbox(v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; size_t v_sz_3876_; size_t v___x_3877_; lean_object* v___x_3878_; lean_object* v_fst_3879_; 
lean_inc_ref(v_args_3871_);
lean_dec_ref(v_x_3870_);
v___x_3874_ = lean_box(0);
v___x_3875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3876_ = lean_array_size(v_args_3871_);
v___x_3877_ = ((size_t)0ULL);
v___x_3878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3869_, v_args_3871_, v_sz_3876_, v___x_3877_, v___x_3875_);
lean_dec_ref(v_args_3871_);
v_fst_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_fst_3879_);
lean_dec_ref(v___x_3878_);
if (lean_obj_tag(v_fst_3879_) == 0)
{
return v___x_3874_;
}
else
{
lean_object* v_val_3880_; 
v_val_3880_ = lean_ctor_get(v_fst_3879_, 0);
lean_inc(v_val_3880_);
lean_dec_ref(v_fst_3879_);
return v_val_3880_;
}
}
else
{
lean_object* v___x_3881_; 
lean_dec_ref(v_p_3869_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v_x_3870_);
return v___x_3881_;
}
}
else
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
lean_inc(v_x_3870_);
v___x_3882_ = lean_apply_1(v_p_3869_, v_x_3870_);
v___x_3883_ = lean_unbox(v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_dec(v_x_3870_);
v___x_3884_ = lean_box(0);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v_x_3870_);
return v___x_3885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3886_, lean_object* v_as_3887_, size_t v_sz_3888_, size_t v_i_3889_, lean_object* v_b_3890_){
_start:
{
uint8_t v___x_3891_; 
v___x_3891_ = lean_usize_dec_lt(v_i_3889_, v_sz_3888_);
if (v___x_3891_ == 0)
{
lean_dec_ref(v_p_3886_);
return v_b_3890_;
}
else
{
lean_object* v___x_3892_; lean_object* v_a_3893_; lean_object* v___x_3894_; 
lean_dec_ref(v_b_3890_);
v___x_3892_ = lean_box(0);
v_a_3893_ = lean_array_uget_borrowed(v_as_3887_, v_i_3889_);
lean_inc(v_a_3893_);
lean_inc_ref(v_p_3886_);
v___x_3894_ = l_Lean_Syntax_findAux(v_p_3886_, v_a_3893_);
if (lean_obj_tag(v___x_3894_) == 1)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_dec_ref(v_p_3886_);
v___x_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
lean_ctor_set(v___x_3896_, 1, v___x_3892_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; size_t v___x_3898_; size_t v___x_3899_; 
lean_dec(v___x_3894_);
v___x_3897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3889_, v___x_3898_);
v_i_3889_ = v___x_3899_;
v_b_3890_ = v___x_3897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3901_, lean_object* v_as_3902_, lean_object* v_sz_3903_, lean_object* v_i_3904_, lean_object* v_b_3905_){
_start:
{
size_t v_sz_boxed_3906_; size_t v_i_boxed_3907_; lean_object* v_res_3908_; 
v_sz_boxed_3906_ = lean_unbox_usize(v_sz_3903_);
lean_dec(v_sz_3903_);
v_i_boxed_3907_ = lean_unbox_usize(v_i_3904_);
lean_dec(v_i_3904_);
v_res_3908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3901_, v_as_3902_, v_sz_boxed_3906_, v_i_boxed_3907_, v_b_3905_);
lean_dec_ref(v_as_3902_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3909_, lean_object* v_p_3910_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Syntax_findAux(v_p_3910_, v_stx_3909_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Syntax_isNatLit_x3f(v_s_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v___x_3914_; 
v___x_3914_ = lean_unsigned_to_nat(0u);
return v___x_3914_;
}
else
{
lean_object* v_val_3915_; 
v_val_3915_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_val_3915_);
lean_dec_ref(v___x_3913_);
return v_val_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lean_TSyntax_getNat(v_s_3916_);
lean_dec(v_s_3916_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3921_){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3923_ = l_Lean_Syntax_isLit_x3f(v___x_3922_, v_stx_3921_);
if (lean_obj_tag(v___x_3923_) == 1)
{
lean_object* v_val_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_val_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_val_3924_);
lean_dec_ref(v___x_3923_);
v___x_3925_ = lean_unsigned_to_nat(0u);
v___x_3926_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3924_, v___x_3925_, v___x_3925_);
lean_dec(v_val_3924_);
return v___x_3926_;
}
else
{
lean_object* v___x_3927_; 
lean_dec(v___x_3923_);
v___x_3927_ = lean_box(0);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3928_);
lean_dec(v_stx_3928_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_unsigned_to_nat(0u);
return v___x_3932_;
}
else
{
lean_object* v_val_3933_; 
v_val_3933_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_val_3933_);
lean_dec_ref(v___x_3931_);
return v_val_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_TSyntax_getHexNumVal(v_s_3934_);
lean_dec(v_s_3934_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3936_, lean_object* v_p_3937_, lean_object* v_n_3938_){
_start:
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_string_utf8_at_end(v_s_3936_, v_p_3937_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; uint32_t v___x_3941_; uint32_t v___x_3942_; uint8_t v___x_3943_; 
v___x_3940_ = lean_string_utf8_next(v_s_3936_, v_p_3937_);
v___x_3941_ = lean_string_utf8_get(v_s_3936_, v_p_3937_);
lean_dec(v_p_3937_);
v___x_3942_ = 95;
v___x_3943_ = lean_uint32_dec_eq(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_3945_ = lean_nat_add(v_n_3938_, v___x_3944_);
lean_dec(v_n_3938_);
v_p_3937_ = v___x_3940_;
v_n_3938_ = v___x_3945_;
goto _start;
}
else
{
v_p_3937_ = v___x_3940_;
goto _start;
}
}
else
{
lean_dec(v_p_3937_);
return v_n_3938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3948_, lean_object* v_p_3949_, lean_object* v_n_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3948_, v_p_3949_, v_n_3950_);
lean_dec_ref(v_s_3948_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3952_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3954_ = l_Lean_Syntax_isLit_x3f(v___x_3953_, v_s_3952_);
if (lean_obj_tag(v___x_3954_) == 1)
{
lean_object* v_val_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_val_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_val_3955_);
lean_dec_ref(v___x_3954_);
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_3957_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3955_, v___x_3956_, v___x_3956_);
lean_dec(v_val_3955_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; 
lean_dec(v___x_3954_);
v___x_3958_ = lean_unsigned_to_nat(0u);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_TSyntax_getHexNumSize(v_s_3959_);
lean_dec(v_s_3959_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_Lean_Syntax_getId(v_s_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_TSyntax_getId(v_s_3963_);
lean_dec(v_s_3963_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3972_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3974_; 
v___x_3974_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_TSyntax_getScientific(v_s_3976_);
lean_dec(v_s_3976_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_Syntax_isStrLit_x3f(v_s_3978_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; 
v___x_3980_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3980_;
}
else
{
lean_object* v_val_3981_; 
v_val_3981_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3981_);
lean_dec_ref(v___x_3979_);
return v_val_3981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_TSyntax_getString(v_s_3982_);
lean_dec(v_s_3982_);
return v_res_3983_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3984_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l_Lean_Syntax_isCharLit_x3f(v_s_3984_);
if (lean_obj_tag(v___x_3985_) == 0)
{
uint32_t v___x_3986_; 
v___x_3986_ = 65;
return v___x_3986_;
}
else
{
lean_object* v_val_3987_; uint32_t v___x_3988_; 
v_val_3987_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_val_3987_);
lean_dec_ref(v___x_3985_);
v___x_3988_ = lean_unbox_uint32(v_val_3987_);
lean_dec(v_val_3987_);
return v___x_3988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3989_){
_start:
{
uint32_t v_res_3990_; lean_object* v_r_3991_; 
v_res_3990_ = l_Lean_TSyntax_getChar(v_s_3989_);
lean_dec(v_s_3989_);
v_r_3991_ = lean_box_uint32(v_res_3990_);
return v_r_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3992_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_Syntax_isNameLit_x3f(v_s_3992_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_box(0);
return v___x_3994_;
}
else
{
lean_object* v_val_3995_; 
v_val_3995_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_val_3995_);
lean_dec_ref(v___x_3993_);
return v_val_3995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_TSyntax_getName(v_s_3996_);
lean_dec(v_s_3996_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3998_){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = lean_unsigned_to_nat(0u);
v___x_4000_ = l_Lean_Syntax_getArg(v_s_3998_, v___x_3999_);
v___x_4001_ = l_Lean_Syntax_getId(v___x_4000_);
lean_dec(v___x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_TSyntax_getHygieneInfo(v_s_4002_);
lean_dec(v_s_4002_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Syntax_SepArray_ofElems(v_sep_4004_, v_a_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_4007_, v_a_4008_);
lean_dec_ref(v_a_4008_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_4010_){
_start:
{
lean_object* v___f_4011_; 
v___f_4011_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4011_, 0, v_sep_4010_);
return v___f_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_4012_, lean_object* v_sep_4013_){
_start:
{
lean_object* v___f_4014_; 
v___f_4014_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4014_, 0, v_sep_4013_);
return v___f_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_4015_, lean_object* v_sep_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_4015_, v_sep_4016_);
lean_dec(v_k_4015_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_4018_, lean_object* v_val_4019_, uint8_t v_canonical_4020_){
_start:
{
lean_object* v___x_4021_; lean_object* v_src_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v_imported_4025_; lean_object* v_ctx_4026_; lean_object* v_scopes_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4043_; 
v___x_4021_ = lean_unsigned_to_nat(0u);
v_src_4022_ = l_Lean_Syntax_getArg(v_s_4018_, v___x_4021_);
v___x_4023_ = l_Lean_Syntax_getId(v_src_4022_);
v___x_4024_ = l_Lean_extractMacroScopes(v___x_4023_);
v_imported_4025_ = lean_ctor_get(v___x_4024_, 1);
v_ctx_4026_ = lean_ctor_get(v___x_4024_, 2);
v_scopes_4027_ = lean_ctor_get(v___x_4024_, 3);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4043_ == 0)
{
lean_object* v_unused_4044_; 
v_unused_4044_ = lean_ctor_get(v___x_4024_, 0);
lean_dec(v_unused_4044_);
v___x_4029_ = v___x_4024_;
v_isShared_4030_ = v_isSharedCheck_4043_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_scopes_4027_);
lean_inc(v_ctx_4026_);
lean_inc(v_imported_4025_);
lean_dec(v___x_4024_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4043_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4033_; 
lean_inc(v_val_4019_);
v___x_4031_ = lean_erase_macro_scopes(v_val_4019_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4031_);
v___x_4033_ = v___x_4029_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4031_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_imported_4025_);
lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_ctx_4026_);
lean_ctor_set(v_reuseFailAlloc_4042_, 3, v_scopes_4027_);
v___x_4033_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v_id_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_id_4034_ = l_Lean_MacroScopesView_review(v___x_4033_);
v___x_4035_ = l_Lean_SourceInfo_fromRef(v_src_4022_, v_canonical_4020_);
lean_dec(v_src_4022_);
v___x_4036_ = 1;
v___x_4037_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_4019_, v___x_4036_);
v___x_4038_ = lean_string_utf8_byte_size(v___x_4037_);
v___x_4039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4021_);
lean_ctor_set(v___x_4039_, 2, v___x_4038_);
v___x_4040_ = lean_box(0);
v___x_4041_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4035_);
lean_ctor_set(v___x_4041_, 1, v___x_4039_);
lean_ctor_set(v___x_4041_, 2, v_id_4034_);
lean_ctor_set(v___x_4041_, 3, v___x_4040_);
return v___x_4041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4045_, lean_object* v_val_4046_, lean_object* v_canonical_4047_){
_start:
{
uint8_t v_canonical_boxed_4048_; lean_object* v_res_4049_; 
v_canonical_boxed_4048_ = lean_unbox(v_canonical_4047_);
v_res_4049_ = l_Lean_HygieneInfo_mkIdent(v_s_4045_, v_val_4046_, v_canonical_boxed_4048_);
lean_dec(v_s_4045_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_apply_1(v_inst_4050_, v_a_4052_);
v___x_4054_ = lean_apply_1(v_inst_4051_, v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4055_, lean_object* v_inst_4056_){
_start:
{
lean_object* v___f_4057_; 
v___f_4057_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4057_, 0, v_inst_4055_);
lean_closure_set(v___f_4057_, 1, v_inst_4056_);
return v___f_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4058_, lean_object* v_k_4059_, lean_object* v_k_x27_4060_, lean_object* v_inst_4061_, lean_object* v_inst_4062_){
_start:
{
lean_object* v___f_4063_; 
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4063_, 0, v_inst_4061_);
lean_closure_set(v___f_4063_, 1, v_inst_4062_);
return v___f_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4064_, lean_object* v_k_4065_, lean_object* v_k_x27_4066_, lean_object* v_inst_4067_, lean_object* v_inst_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4064_, v_k_4065_, v_k_x27_4066_, v_inst_4067_, v_inst_4068_);
lean_dec(v_k_x27_4066_);
lean_dec(v_k_4065_);
return v_res_4069_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4078_ = l_Lean_mkCIdent(v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4084_ = l_Lean_mkCIdent(v___x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4085_){
_start:
{
if (v_x_4085_ == 0)
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4086_;
}
else
{
lean_object* v___x_4087_; 
v___x_4087_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4088_){
_start:
{
uint8_t v_x_85__boxed_4089_; lean_object* v_res_4090_; 
v_x_85__boxed_4089_ = lean_unbox(v_x_4088_);
v_res_4090_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4089_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4093_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_box(2);
v___x_4095_ = l_Lean_Syntax_mkCharLit(v_val_4093_, v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4096_){
_start:
{
uint32_t v_val_boxed_4097_; lean_object* v_res_4098_; 
v_val_boxed_4097_ = lean_unbox_uint32(v_val_4096_);
lean_dec(v_val_4096_);
v_res_4098_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4097_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4101_){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = lean_box(2);
v___x_4103_ = l_Lean_Syntax_mkStrLit(v_val_4101_, v___x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4106_){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = l_Nat_reprFast(v_n_4106_);
v___x_4108_ = lean_box(2);
v___x_4109_ = l_Lean_Syntax_mkNumLit(v___x_4107_, v___x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4117_){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4118_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4119_ = lean_substring_tostring(v_s_4117_);
v___x_4120_ = lean_box(2);
v___x_4121_ = l_Lean_Syntax_mkStrLit(v___x_4119_, v___x_4120_);
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = lean_mk_empty_array_with_capacity(v___x_4122_);
v___x_4124_ = lean_array_push(v___x_4123_, v___x_4121_);
v___x_4125_ = l_Lean_Syntax_mkCApp(v___x_4118_, v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4128_, lean_object* v_x_4129_){
_start:
{
switch(lean_obj_tag(v_x_4129_))
{
case 0:
{
uint8_t v___x_4130_; 
v___x_4130_ = l_List_isEmpty___redArg(v_acc_4128_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4131_, 0, v_acc_4128_);
return v___x_4131_;
}
else
{
lean_object* v___x_4132_; 
lean_dec(v_acc_4128_);
v___x_4132_ = lean_box(0);
return v___x_4132_;
}
}
case 1:
{
lean_object* v_pre_4133_; lean_object* v_str_4134_; lean_object* v_val_4136_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v_pre_4133_ = lean_ctor_get(v_x_4129_, 0);
lean_inc(v_pre_4133_);
v_str_4134_ = lean_ctor_get(v_x_4129_, 1);
lean_inc_ref(v_str_4134_);
lean_dec_ref(v_x_4129_);
v___x_4139_ = lean_unsigned_to_nat(0u);
v___x_4140_ = lean_string_utf8_byte_size(v_str_4134_);
v___x_4141_ = lean_nat_dec_lt(v___x_4139_, v___x_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4142_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4143_ = lean_string_append(v___x_4142_, v_str_4134_);
lean_dec_ref(v_str_4134_);
v___x_4144_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4145_ = lean_string_append(v___x_4143_, v___x_4144_);
v_val_4136_ = v___x_4145_;
goto v___jp_4135_;
}
else
{
lean_object* v___f_4146_; lean_object* v___f_4147_; uint8_t v___y_4161_; uint32_t v___y_4163_; uint8_t v___y_4164_; uint32_t v___y_4169_; uint8_t v___y_4175_; uint8_t v_c_4184_; uint8_t v___y_4186_; uint8_t v___y_4190_; uint8_t v___x_4195_; uint8_t v___x_4196_; 
v___f_4146_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v___f_4147_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v_c_4184_ = lean_string_get_byte_fast(v_str_4134_, v___x_4139_);
v___x_4195_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4196_ = lean_uint8_dec_le(v___x_4195_, v_c_4184_);
if (v___x_4196_ == 0)
{
v___y_4190_ = v___x_4196_;
goto v___jp_4189_;
}
else
{
uint8_t v___x_4197_; uint8_t v___x_4198_; 
v___x_4197_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4198_ = lean_uint8_dec_le(v_c_4184_, v___x_4197_);
v___y_4190_ = v___x_4198_;
goto v___jp_4189_;
}
v___jp_4148_:
{
uint8_t v___x_4149_; 
lean_inc_ref(v_str_4134_);
v___x_4149_ = lean_string_any(v_str_4134_, v___f_4147_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4150_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4151_ = lean_string_append(v___x_4150_, v_str_4134_);
lean_dec_ref(v_str_4134_);
v___x_4152_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4153_ = lean_string_append(v___x_4151_, v___x_4152_);
v_val_4136_ = v___x_4153_;
goto v___jp_4135_;
}
else
{
lean_object* v___x_4154_; 
lean_dec_ref(v_str_4134_);
lean_dec(v_pre_4133_);
lean_dec(v_acc_4128_);
v___x_4154_ = lean_box(0);
return v___x_4154_;
}
}
v___jp_4155_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; 
lean_inc_ref(v_str_4134_);
v___x_4156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4156_, 0, v_str_4134_);
lean_ctor_set(v___x_4156_, 1, v___x_4139_);
lean_ctor_set(v___x_4156_, 2, v___x_4140_);
v___x_4157_ = lean_unsigned_to_nat(1u);
v___x_4158_ = lean_substring_drop(v___x_4156_, v___x_4157_);
v___x_4159_ = lean_substring_all(v___x_4158_, v___f_4146_);
if (v___x_4159_ == 0)
{
goto v___jp_4148_;
}
else
{
v_val_4136_ = v_str_4134_;
goto v___jp_4135_;
}
}
v___jp_4160_:
{
if (v___y_4161_ == 0)
{
goto v___jp_4148_;
}
else
{
goto v___jp_4155_;
}
}
v___jp_4162_:
{
if (v___y_4164_ == 0)
{
uint32_t v___x_4165_; uint8_t v___x_4166_; 
v___x_4165_ = 95;
v___x_4166_ = lean_uint32_dec_eq(v___y_4163_, v___x_4165_);
if (v___x_4166_ == 0)
{
uint8_t v___x_4167_; 
v___x_4167_ = l_Lean_isLetterLike(v___y_4163_);
v___y_4161_ = v___x_4167_;
goto v___jp_4160_;
}
else
{
v___y_4161_ = v___x_4166_;
goto v___jp_4160_;
}
}
else
{
goto v___jp_4155_;
}
}
v___jp_4168_:
{
uint32_t v___x_4170_; uint8_t v___x_4171_; 
v___x_4170_ = 97;
v___x_4171_ = lean_uint32_dec_le(v___x_4170_, v___y_4169_);
if (v___x_4171_ == 0)
{
v___y_4163_ = v___y_4169_;
v___y_4164_ = v___x_4171_;
goto v___jp_4162_;
}
else
{
uint32_t v___x_4172_; uint8_t v___x_4173_; 
v___x_4172_ = 122;
v___x_4173_ = lean_uint32_dec_le(v___y_4169_, v___x_4172_);
v___y_4163_ = v___y_4169_;
v___y_4164_ = v___x_4173_;
goto v___jp_4162_;
}
}
v___jp_4174_:
{
if (v___y_4175_ == 0)
{
uint32_t v___x_4176_; uint32_t v___x_4177_; uint8_t v___x_4178_; 
v___x_4176_ = lean_string_utf8_get(v_str_4134_, v___x_4139_);
v___x_4177_ = 65;
v___x_4178_ = lean_uint32_dec_le(v___x_4177_, v___x_4176_);
if (v___x_4178_ == 0)
{
v___y_4169_ = v___x_4176_;
goto v___jp_4168_;
}
else
{
uint32_t v___x_4179_; uint8_t v___x_4180_; 
v___x_4179_ = 90;
v___x_4180_ = lean_uint32_dec_le(v___x_4176_, v___x_4179_);
if (v___x_4180_ == 0)
{
v___y_4169_ = v___x_4176_;
goto v___jp_4168_;
}
else
{
goto v___jp_4155_;
}
}
}
else
{
v_val_4136_ = v_str_4134_;
goto v___jp_4135_;
}
}
v___jp_4181_:
{
lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = lean_unsigned_to_nat(1u);
v___x_4183_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4134_, v___x_4182_);
v___y_4175_ = v___x_4183_;
goto v___jp_4174_;
}
v___jp_4185_:
{
if (v___y_4186_ == 0)
{
uint8_t v___x_4187_; uint8_t v___x_4188_; 
v___x_4187_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4188_ = lean_uint8_dec_eq(v_c_4184_, v___x_4187_);
if (v___x_4188_ == 0)
{
v___y_4175_ = v___x_4188_;
goto v___jp_4174_;
}
else
{
goto v___jp_4181_;
}
}
else
{
goto v___jp_4181_;
}
}
v___jp_4189_:
{
if (v___y_4190_ == 0)
{
uint8_t v___x_4191_; uint8_t v___x_4192_; 
v___x_4191_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4192_ = lean_uint8_dec_le(v___x_4191_, v_c_4184_);
if (v___x_4192_ == 0)
{
v___y_4186_ = v___x_4192_;
goto v___jp_4185_;
}
else
{
uint8_t v___x_4193_; uint8_t v___x_4194_; 
v___x_4193_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4194_ = lean_uint8_dec_le(v_c_4184_, v___x_4193_);
v___y_4186_ = v___x_4194_;
goto v___jp_4185_;
}
}
else
{
goto v___jp_4181_;
}
}
}
v___jp_4135_:
{
lean_object* v___x_4137_; 
v___x_4137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4137_, 0, v_val_4136_);
lean_ctor_set(v___x_4137_, 1, v_acc_4128_);
v_acc_4128_ = v___x_4137_;
v_x_4129_ = v_pre_4133_;
goto _start;
}
}
default: 
{
lean_object* v___x_4199_; 
lean_dec_ref(v_x_4129_);
lean_dec(v_acc_4128_);
v___x_4199_ = lean_box(0);
return v___x_4199_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4207_ = l_Lean_mkCIdent(v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4218_){
_start:
{
switch(lean_obj_tag(v_x_4218_))
{
case 0:
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4219_;
}
case 1:
{
lean_object* v_pre_4220_; lean_object* v_str_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v_pre_4220_ = lean_ctor_get(v_x_4218_, 0);
lean_inc(v_pre_4220_);
v_str_4221_ = lean_ctor_get(v_x_4218_, 1);
lean_inc_ref(v_str_4221_);
lean_dec_ref(v_x_4218_);
v___x_4222_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4223_ = l_Lean_quoteNameMk(v_pre_4220_);
v___x_4224_ = lean_box(2);
v___x_4225_ = l_Lean_Syntax_mkStrLit(v_str_4221_, v___x_4224_);
v___x_4226_ = lean_unsigned_to_nat(2u);
v___x_4227_ = lean_mk_empty_array_with_capacity(v___x_4226_);
v___x_4228_ = lean_array_push(v___x_4227_, v___x_4223_);
v___x_4229_ = lean_array_push(v___x_4228_, v___x_4225_);
v___x_4230_ = l_Lean_Syntax_mkCApp(v___x_4222_, v___x_4229_);
return v___x_4230_;
}
default: 
{
lean_object* v_pre_4231_; lean_object* v_i_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_pre_4231_ = lean_ctor_get(v_x_4218_, 0);
lean_inc(v_pre_4231_);
v_i_4232_ = lean_ctor_get(v_x_4218_, 1);
lean_inc(v_i_4232_);
lean_dec_ref(v_x_4218_);
v___x_4233_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4234_ = l_Lean_quoteNameMk(v_pre_4231_);
v___x_4235_ = l_Nat_reprFast(v_i_4232_);
v___x_4236_ = lean_box(2);
v___x_4237_ = l_Lean_Syntax_mkNumLit(v___x_4235_, v___x_4236_);
v___x_4238_ = lean_unsigned_to_nat(2u);
v___x_4239_ = lean_mk_empty_array_with_capacity(v___x_4238_);
v___x_4240_ = lean_array_push(v___x_4239_, v___x_4234_);
v___x_4241_ = lean_array_push(v___x_4240_, v___x_4237_);
v___x_4242_ = l_Lean_Syntax_mkCApp(v___x_4233_, v___x_4241_);
return v___x_4242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4249_){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_box(0);
lean_inc(v_n_4249_);
v___x_4251_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4250_, v_n_4249_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_quoteNameMk(v_n_4249_);
return v___x_4252_;
}
else
{
lean_object* v_val_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_dec(v_n_4249_);
v_val_4253_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_val_4253_);
lean_dec_ref(v___x_4251_);
v___x_4254_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4255_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4256_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4257_ = lean_string_intercalate(v___x_4256_, v_val_4253_);
v___x_4258_ = lean_string_append(v___x_4255_, v___x_4257_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = lean_box(2);
v___x_4260_ = l_Lean_Syntax_mkNameLit(v___x_4258_, v___x_4259_);
v___x_4261_ = lean_unsigned_to_nat(1u);
v___x_4262_ = lean_mk_empty_array_with_capacity(v___x_4261_);
v___x_4263_ = lean_array_push(v___x_4262_, v___x_4260_);
v___x_4264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4259_);
lean_ctor_set(v___x_4264_, 1, v___x_4254_);
lean_ctor_set(v___x_4264_, 2, v___x_4263_);
return v___x_4264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4272_, lean_object* v_inst_4273_, lean_object* v_x_4274_){
_start:
{
lean_object* v_fst_4275_; lean_object* v_snd_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v_fst_4275_ = lean_ctor_get(v_x_4274_, 0);
lean_inc(v_fst_4275_);
v_snd_4276_ = lean_ctor_get(v_x_4274_, 1);
lean_inc(v_snd_4276_);
lean_dec_ref(v_x_4274_);
v___x_4277_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4278_ = lean_apply_1(v_inst_4272_, v_fst_4275_);
v___x_4279_ = lean_apply_1(v_inst_4273_, v_snd_4276_);
v___x_4280_ = lean_unsigned_to_nat(2u);
v___x_4281_ = lean_mk_empty_array_with_capacity(v___x_4280_);
v___x_4282_ = lean_array_push(v___x_4281_, v___x_4278_);
v___x_4283_ = lean_array_push(v___x_4282_, v___x_4279_);
v___x_4284_ = l_Lean_Syntax_mkCApp(v___x_4277_, v___x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4285_, lean_object* v_inst_4286_){
_start:
{
lean_object* v___f_4287_; 
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4287_, 0, v_inst_4285_);
lean_closure_set(v___f_4287_, 1, v_inst_4286_);
return v___f_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4288_, lean_object* v_00_u03b2_4289_, lean_object* v_inst_4290_, lean_object* v_inst_4291_){
_start:
{
lean_object* v___f_4292_; 
v___f_4292_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4292_, 0, v_inst_4290_);
lean_closure_set(v___f_4292_, 1, v_inst_4291_);
return v___f_4292_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4299_ = l_Lean_mkCIdent(v___x_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4304_, lean_object* v_x_4305_){
_start:
{
if (lean_obj_tag(v_x_4305_) == 0)
{
lean_object* v___x_4306_; 
lean_dec_ref(v_inst_4304_);
v___x_4306_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4306_;
}
else
{
lean_object* v_head_4307_; lean_object* v_tail_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v_head_4307_ = lean_ctor_get(v_x_4305_, 0);
lean_inc(v_head_4307_);
v_tail_4308_ = lean_ctor_get(v_x_4305_, 1);
lean_inc(v_tail_4308_);
lean_dec_ref(v_x_4305_);
v___x_4309_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4304_);
v___x_4310_ = lean_apply_1(v_inst_4304_, v_head_4307_);
v___x_4311_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4304_, v_tail_4308_);
v___x_4312_ = lean_unsigned_to_nat(2u);
v___x_4313_ = lean_mk_empty_array_with_capacity(v___x_4312_);
v___x_4314_ = lean_array_push(v___x_4313_, v___x_4310_);
v___x_4315_ = lean_array_push(v___x_4314_, v___x_4311_);
v___x_4316_ = l_Lean_Syntax_mkCApp(v___x_4309_, v___x_4315_);
return v___x_4316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4317_, lean_object* v_inst_4318_, lean_object* v_x_4319_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4318_, v_x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4321_, v_a_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4324_, lean_object* v_inst_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4325_, v_a_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4329_, 0, lean_box(0));
lean_closure_set(v___x_4329_, 1, v_inst_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4330_, lean_object* v_inst_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4332_, 0, lean_box(0));
lean_closure_set(v___x_4332_, 1, v_inst_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4335_, lean_object* v_xs_4336_, lean_object* v_i_4337_, lean_object* v_args_4338_){
_start:
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = lean_array_get_size(v_xs_4336_);
v___x_4340_ = lean_nat_dec_lt(v_i_4337_, v___x_4339_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_dec(v_i_4337_);
lean_dec_ref(v_inst_4335_);
v___x_4341_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4342_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4343_ = l_Nat_reprFast(v___x_4339_);
v___x_4344_ = lean_string_append(v___x_4342_, v___x_4343_);
lean_dec_ref(v___x_4343_);
v___x_4345_ = l_Lean_Name_mkStr2(v___x_4341_, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_mkCApp(v___x_4345_, v_args_4338_);
return v___x_4346_;
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4347_ = lean_unsigned_to_nat(1u);
v___x_4348_ = lean_nat_add(v_i_4337_, v___x_4347_);
v___x_4349_ = lean_array_fget_borrowed(v_xs_4336_, v_i_4337_);
lean_dec(v_i_4337_);
lean_inc_ref(v_inst_4335_);
lean_inc(v___x_4349_);
v___x_4350_ = lean_apply_1(v_inst_4335_, v___x_4349_);
v___x_4351_ = lean_array_push(v_args_4338_, v___x_4350_);
v_i_4337_ = v___x_4348_;
v_args_4338_ = v___x_4351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4353_, lean_object* v_xs_4354_, lean_object* v_i_4355_, lean_object* v_args_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4353_, v_xs_4354_, v_i_4355_, v_args_4356_);
lean_dec_ref(v_xs_4354_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4358_, lean_object* v_inst_4359_, lean_object* v_xs_4360_, lean_object* v_i_4361_, lean_object* v_args_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4359_, v_xs_4360_, v_i_4361_, v_args_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4364_, lean_object* v_inst_4365_, lean_object* v_xs_4366_, lean_object* v_i_4367_, lean_object* v_args_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4364_, v_inst_4365_, v_xs_4366_, v_i_4367_, v_args_4368_);
lean_dec_ref(v_xs_4366_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4374_, lean_object* v_xs_4375_){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4376_ = lean_array_get_size(v_xs_4375_);
v___x_4377_ = lean_unsigned_to_nat(8u);
v___x_4378_ = lean_nat_dec_le(v___x_4376_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4379_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4380_ = lean_array_to_list(v_xs_4375_);
v___x_4381_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4374_, v___x_4380_);
v___x_4382_ = lean_unsigned_to_nat(1u);
v___x_4383_ = lean_mk_empty_array_with_capacity(v___x_4382_);
v___x_4384_ = lean_array_push(v___x_4383_, v___x_4381_);
v___x_4385_ = l_Lean_Syntax_mkCApp(v___x_4379_, v___x_4384_);
return v___x_4385_;
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4386_ = lean_unsigned_to_nat(0u);
v___x_4387_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4388_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4374_, v_xs_4375_, v___x_4386_, v___x_4387_);
lean_dec_ref(v_xs_4375_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4389_, lean_object* v_inst_4390_, lean_object* v_xs_4391_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4390_, v_xs_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4393_, lean_object* v_xs_4394_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4393_, v_xs_4394_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4396_, lean_object* v_inst_4397_, lean_object* v_xs_4398_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4397_, v_xs_4398_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4400_){
_start:
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4401_, 0, lean_box(0));
lean_closure_set(v___x_4401_, 1, v_inst_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4402_, lean_object* v_inst_4403_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4404_, 0, lean_box(0));
lean_closure_set(v___x_4404_, 1, v_inst_4403_);
return v___x_4404_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4411_ = lean_mk_syntax_ident(v___x_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4416_, lean_object* v_x_4417_){
_start:
{
if (lean_obj_tag(v_x_4417_) == 0)
{
lean_object* v___x_4418_; 
lean_dec_ref(v_inst_4416_);
v___x_4418_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4418_;
}
else
{
lean_object* v_val_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_val_4419_ = lean_ctor_get(v_x_4417_, 0);
lean_inc(v_val_4419_);
lean_dec_ref(v_x_4417_);
v___x_4420_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4421_ = lean_apply_1(v_inst_4416_, v_val_4419_);
v___x_4422_ = lean_unsigned_to_nat(1u);
v___x_4423_ = lean_mk_empty_array_with_capacity(v___x_4422_);
v___x_4424_ = lean_array_push(v___x_4423_, v___x_4421_);
v___x_4425_ = l_Lean_Syntax_mkCApp(v___x_4420_, v___x_4424_);
return v___x_4425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4426_){
_start:
{
lean_object* v___f_4427_; 
v___f_4427_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4427_, 0, v_inst_4426_);
return v___f_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4428_, lean_object* v_inst_4429_){
_start:
{
lean_object* v___f_4430_; 
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4430_, 0, v_inst_4429_);
return v___f_4430_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4431_, lean_object* v_k_4432_){
_start:
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4434_ = lean_name_eq(v_k_4432_, v___x_4433_);
if (v___x_4434_ == 0)
{
uint8_t v___x_4435_; 
v___x_4435_ = 1;
return v___x_4435_;
}
else
{
return v___x_4431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4436_, lean_object* v_k_4437_){
_start:
{
uint8_t v___x_437__boxed_4438_; uint8_t v_res_4439_; lean_object* v_r_4440_; 
v___x_437__boxed_4438_ = lean_unbox(v___x_4436_);
v_res_4439_ = l_Lean_evalPrec___lam__0(v___x_437__boxed_4438_, v_k_4437_);
lean_dec(v_k_4437_);
v_r_4440_ = lean_box(v_res_4439_);
return v_r_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_methods_4445_; lean_object* v_quotContext_4446_; lean_object* v_currMacroScope_4447_; lean_object* v_currRecDepth_4448_; lean_object* v_maxRecDepth_4449_; lean_object* v_ref_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4489_; 
v_methods_4445_ = lean_ctor_get(v_a_4443_, 0);
v_quotContext_4446_ = lean_ctor_get(v_a_4443_, 1);
v_currMacroScope_4447_ = lean_ctor_get(v_a_4443_, 2);
v_currRecDepth_4448_ = lean_ctor_get(v_a_4443_, 3);
v_maxRecDepth_4449_ = lean_ctor_get(v_a_4443_, 4);
v_ref_4450_ = lean_ctor_get(v_a_4443_, 5);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_a_4443_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4452_ = v_a_4443_;
v_isShared_4453_ = v_isSharedCheck_4489_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_ref_4450_);
lean_inc(v_maxRecDepth_4449_);
lean_inc(v_currRecDepth_4448_);
lean_inc(v_currMacroScope_4447_);
lean_inc(v_quotContext_4446_);
lean_inc(v_methods_4445_);
lean_dec(v_a_4443_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4489_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
uint8_t v___x_4454_; 
v___x_4454_ = lean_nat_dec_eq(v_currRecDepth_4448_, v_maxRecDepth_4449_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4460_; 
v___x_4455_ = lean_box(v___x_4454_);
v___f_4456_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4456_, 0, v___x_4455_);
v___x_4457_ = lean_unsigned_to_nat(1u);
v___x_4458_ = lean_nat_add(v_currRecDepth_4448_, v___x_4457_);
lean_dec(v_currRecDepth_4448_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 3, v___x_4458_);
v___x_4460_ = v___x_4452_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_methods_4445_);
lean_ctor_set(v_reuseFailAlloc_4485_, 1, v_quotContext_4446_);
lean_ctor_set(v_reuseFailAlloc_4485_, 2, v_currMacroScope_4447_);
lean_ctor_set(v_reuseFailAlloc_4485_, 3, v___x_4458_);
lean_ctor_set(v_reuseFailAlloc_4485_, 4, v_maxRecDepth_4449_);
lean_ctor_set(v_reuseFailAlloc_4485_, 5, v_ref_4450_);
v___x_4460_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
lean_object* v___x_4461_; 
lean_inc_ref(v___x_4460_);
v___x_4461_ = l_Lean_expandMacros(v_stx_4442_, v___f_4456_, v___x_4460_, v_a_4444_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4475_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
v_a_4463_ = lean_ctor_get(v___x_4461_, 1);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4465_ = v___x_4461_;
v_isShared_4466_ = v_isSharedCheck_4475_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_inc(v_a_4462_);
lean_dec(v___x_4461_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4475_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4467_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4462_);
v___x_4468_ = l_Lean_Syntax_isOfKind(v_a_4462_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_del_object(v___x_4465_);
v___x_4469_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4470_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4462_, v___x_4469_, v___x_4460_, v_a_4463_);
lean_dec(v_a_4462_);
return v___x_4470_;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
lean_dec_ref(v___x_4460_);
v___x_4471_ = l_Lean_TSyntax_getNat(v_a_4462_);
lean_dec(v_a_4462_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4471_);
v___x_4473_ = v___x_4465_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_a_4463_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec_ref(v___x_4460_);
v_a_4476_ = lean_ctor_get(v___x_4461_, 0);
v_a_4477_ = lean_ctor_get(v___x_4461_, 1);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4461_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_inc(v_a_4476_);
lean_dec(v___x_4461_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4476_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_del_object(v___x_4452_);
lean_dec(v_ref_4450_);
lean_dec(v_maxRecDepth_4449_);
lean_dec(v_currRecDepth_4448_);
lean_dec(v_currMacroScope_4447_);
lean_dec(v_quotContext_4446_);
lean_dec(v_methods_4445_);
v___x_4486_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4487_, 0, v_stx_4442_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
v___x_4488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
lean_ctor_set(v___x_4488_, 1, v_a_4444_);
return v___x_4488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_methods_4494_; lean_object* v_quotContext_4495_; lean_object* v_currMacroScope_4496_; lean_object* v_currRecDepth_4497_; lean_object* v_maxRecDepth_4498_; lean_object* v_ref_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4538_; 
v_methods_4494_ = lean_ctor_get(v_a_4492_, 0);
v_quotContext_4495_ = lean_ctor_get(v_a_4492_, 1);
v_currMacroScope_4496_ = lean_ctor_get(v_a_4492_, 2);
v_currRecDepth_4497_ = lean_ctor_get(v_a_4492_, 3);
v_maxRecDepth_4498_ = lean_ctor_get(v_a_4492_, 4);
v_ref_4499_ = lean_ctor_get(v_a_4492_, 5);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_a_4492_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4501_ = v_a_4492_;
v_isShared_4502_ = v_isSharedCheck_4538_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_ref_4499_);
lean_inc(v_maxRecDepth_4498_);
lean_inc(v_currRecDepth_4497_);
lean_inc(v_currMacroScope_4496_);
lean_inc(v_quotContext_4495_);
lean_inc(v_methods_4494_);
lean_dec(v_a_4492_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4538_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
uint8_t v___x_4503_; 
v___x_4503_ = lean_nat_dec_eq(v_currRecDepth_4497_, v_maxRecDepth_4498_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; lean_object* v___f_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4509_; 
v___x_4504_ = lean_box(v___x_4503_);
v___f_4505_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4505_, 0, v___x_4504_);
v___x_4506_ = lean_unsigned_to_nat(1u);
v___x_4507_ = lean_nat_add(v_currRecDepth_4497_, v___x_4506_);
lean_dec(v_currRecDepth_4497_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 3, v___x_4507_);
v___x_4509_ = v___x_4501_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_methods_4494_);
lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_quotContext_4495_);
lean_ctor_set(v_reuseFailAlloc_4534_, 2, v_currMacroScope_4496_);
lean_ctor_set(v_reuseFailAlloc_4534_, 3, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4534_, 4, v_maxRecDepth_4498_);
lean_ctor_set(v_reuseFailAlloc_4534_, 5, v_ref_4499_);
v___x_4509_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4510_; 
lean_inc_ref(v___x_4509_);
v___x_4510_ = l_Lean_expandMacros(v_stx_4491_, v___f_4505_, v___x_4509_, v_a_4493_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4524_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
v_a_4512_ = lean_ctor_get(v___x_4510_, 1);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4514_ = v___x_4510_;
v_isShared_4515_ = v_isSharedCheck_4524_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_inc(v_a_4511_);
lean_dec(v___x_4510_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4524_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4511_);
v___x_4517_ = l_Lean_Syntax_isOfKind(v_a_4511_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_del_object(v___x_4514_);
v___x_4518_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4519_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4511_, v___x_4518_, v___x_4509_, v_a_4512_);
lean_dec(v_a_4511_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4522_; 
lean_dec_ref(v___x_4509_);
v___x_4520_ = l_Lean_TSyntax_getNat(v_a_4511_);
lean_dec(v_a_4511_);
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v___x_4520_);
v___x_4522_ = v___x_4514_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_a_4512_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_a_4525_; lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec_ref(v___x_4509_);
v_a_4525_ = lean_ctor_get(v___x_4510_, 0);
v_a_4526_ = lean_ctor_get(v___x_4510_, 1);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4510_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_inc(v_a_4525_);
lean_dec(v___x_4510_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4525_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_del_object(v___x_4501_);
lean_dec(v_ref_4499_);
lean_dec(v_maxRecDepth_4498_);
lean_dec(v_currRecDepth_4497_);
lean_dec(v_currMacroScope_4496_);
lean_dec(v_quotContext_4495_);
lean_dec(v_methods_4494_);
v___x_4535_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4536_, 0, v_stx_4491_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
lean_ctor_set(v___x_4537_, 1, v_a_4493_);
return v___x_4537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
if (lean_obj_tag(v_x_4539_) == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec_ref(v_a_4540_);
v___x_4542_ = lean_unsigned_to_nat(1000u);
v___x_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
lean_ctor_set(v___x_4543_, 1, v_a_4541_);
return v___x_4543_;
}
else
{
lean_object* v_val_4544_; lean_object* v___x_4545_; 
v_val_4544_ = lean_ctor_get(v_x_4539_, 0);
lean_inc(v_val_4544_);
lean_dec_ref(v_x_4539_);
v___x_4545_ = l_Lean_evalPrio(v_val_4544_, v_a_4540_, v_a_4541_);
return v___x_4545_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4546_, lean_object* v_x1_4547_, lean_object* v_x2_4548_){
_start:
{
lean_object* v_fst_4549_; uint8_t v___x_4550_; 
v_fst_4549_ = lean_ctor_get(v_x1_4547_, 0);
v___x_4550_ = lean_unbox(v_fst_4549_);
if (v___x_4550_ == 0)
{
lean_object* v_snd_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_x2_4548_);
v_snd_4551_ = lean_ctor_get(v_x1_4547_, 1);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_x1_4547_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; 
v_unused_4560_ = lean_ctor_get(v_x1_4547_, 0);
lean_dec(v_unused_4560_);
v___x_4553_ = v_x1_4547_;
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_snd_4551_);
lean_dec(v_x1_4547_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4555_; lean_object* v___x_4557_; 
v___x_4555_ = lean_box(v___x_4546_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4555_);
v___x_4557_ = v___x_4553_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_snd_4551_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
else
{
lean_object* v_snd_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4571_; 
v_snd_4561_ = lean_ctor_get(v_x1_4547_, 1);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_x1_4547_);
if (v_isSharedCheck_4571_ == 0)
{
lean_object* v_unused_4572_; 
v_unused_4572_ = lean_ctor_get(v_x1_4547_, 0);
lean_dec(v_unused_4572_);
v___x_4563_ = v_x1_4547_;
v_isShared_4564_ = v_isSharedCheck_4571_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_snd_4561_);
lean_dec(v_x1_4547_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4571_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4565_ = 0;
v___x_4566_ = lean_array_push(v_snd_4561_, v_x2_4548_);
v___x_4567_ = lean_box(v___x_4565_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v___x_4566_);
lean_ctor_set(v___x_4563_, 0, v___x_4567_);
v___x_4569_ = v___x_4563_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v___x_4566_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4573_, lean_object* v_x1_4574_, lean_object* v_x2_4575_){
_start:
{
uint8_t v___x_96__boxed_4576_; lean_object* v_res_4577_; 
v___x_96__boxed_4576_ = lean_unbox(v___x_4573_);
v_res_4577_ = l_Array_getSepElems___redArg___lam__0(v___x_96__boxed_4576_, v_x1_4574_, v_x2_4575_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4599_){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4602_ = lean_array_get_size(v_as_4599_);
v___x_4603_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4604_ = lean_nat_dec_lt(v___x_4600_, v___x_4602_);
if (v___x_4604_ == 0)
{
lean_dec_ref(v_as_4599_);
return v___x_4601_;
}
else
{
lean_object* v___x_4605_; lean_object* v___f_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4605_ = lean_box(v___x_4604_);
v___f_4606_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4606_, 0, v___x_4605_);
v___x_4607_ = lean_box(v___x_4604_);
v___x_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
lean_ctor_set(v___x_4608_, 1, v___x_4601_);
v___x_4609_ = lean_nat_dec_le(v___x_4602_, v___x_4602_);
if (v___x_4609_ == 0)
{
if (v___x_4604_ == 0)
{
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___f_4606_);
lean_dec_ref(v_as_4599_);
return v___x_4601_;
}
else
{
size_t v___x_4610_; size_t v___x_4611_; lean_object* v___x_4612_; lean_object* v_snd_4613_; 
v___x_4610_ = ((size_t)0ULL);
v___x_4611_ = lean_usize_of_nat(v___x_4602_);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4603_, v___f_4606_, v_as_4599_, v___x_4610_, v___x_4611_, v___x_4608_);
v_snd_4613_ = lean_ctor_get(v___x_4612_, 1);
lean_inc(v_snd_4613_);
lean_dec(v___x_4612_);
return v_snd_4613_;
}
}
else
{
size_t v___x_4614_; size_t v___x_4615_; lean_object* v___x_4616_; lean_object* v_snd_4617_; 
v___x_4614_ = ((size_t)0ULL);
v___x_4615_ = lean_usize_of_nat(v___x_4602_);
v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4603_, v___f_4606_, v_as_4599_, v___x_4614_, v___x_4615_, v___x_4608_);
v_snd_4617_ = lean_ctor_get(v___x_4616_, 1);
lean_inc(v_snd_4617_);
lean_dec(v___x_4616_);
return v_snd_4617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4618_, lean_object* v_as_4619_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4622_ = lean_array_get_size(v_as_4619_);
v___x_4623_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4624_ = lean_nat_dec_lt(v___x_4620_, v___x_4622_);
if (v___x_4624_ == 0)
{
lean_dec_ref(v_as_4619_);
return v___x_4621_;
}
else
{
lean_object* v___x_4625_; lean_object* v___f_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
v___x_4625_ = lean_box(v___x_4624_);
v___f_4626_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4626_, 0, v___x_4625_);
v___x_4627_ = lean_box(v___x_4624_);
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
lean_ctor_set(v___x_4628_, 1, v___x_4621_);
v___x_4629_ = lean_nat_dec_le(v___x_4622_, v___x_4622_);
if (v___x_4629_ == 0)
{
if (v___x_4624_ == 0)
{
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___f_4626_);
lean_dec_ref(v_as_4619_);
return v___x_4621_;
}
else
{
size_t v___x_4630_; size_t v___x_4631_; lean_object* v___x_4632_; lean_object* v_snd_4633_; 
v___x_4630_ = ((size_t)0ULL);
v___x_4631_ = lean_usize_of_nat(v___x_4622_);
v___x_4632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4623_, v___f_4626_, v_as_4619_, v___x_4630_, v___x_4631_, v___x_4628_);
v_snd_4633_ = lean_ctor_get(v___x_4632_, 1);
lean_inc(v_snd_4633_);
lean_dec(v___x_4632_);
return v_snd_4633_;
}
}
else
{
size_t v___x_4634_; size_t v___x_4635_; lean_object* v___x_4636_; lean_object* v_snd_4637_; 
v___x_4634_ = ((size_t)0ULL);
v___x_4635_ = lean_usize_of_nat(v___x_4622_);
v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4623_, v___f_4626_, v_as_4619_, v___x_4634_, v___x_4635_, v___x_4628_);
v_snd_4637_ = lean_ctor_get(v___x_4636_, 1);
lean_inc(v_snd_4637_);
lean_dec(v___x_4636_);
return v_snd_4637_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4638_, lean_object* v_inst_4639_, lean_object* v_a_4640_, lean_object* v_p_4641_, lean_object* v_acc_4642_, lean_object* v_stx_4643_, uint8_t v_____do__lift_4644_){
_start:
{
if (v_____do__lift_4644_ == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
lean_dec(v_stx_4643_);
v___x_4653_ = lean_unsigned_to_nat(2u);
v___x_4654_ = lean_nat_add(v_i_4638_, v___x_4653_);
v___x_4655_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4639_, v_a_4640_, v_p_4641_, v___x_4654_, v_acc_4642_);
return v___x_4655_;
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; 
v___x_4656_ = lean_array_get_size(v_acc_4642_);
v___x_4657_ = lean_unsigned_to_nat(0u);
v___x_4658_ = lean_nat_dec_eq(v___x_4656_, v___x_4657_);
if (v___x_4658_ == 0)
{
uint8_t v___x_4659_; 
v___x_4659_ = lean_nat_dec_eq(v_i_4638_, v___x_4657_);
if (v___x_4659_ == 0)
{
goto v___jp_4645_;
}
else
{
if (v___x_4658_ == 0)
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4660_ = lean_unsigned_to_nat(2u);
v___x_4661_ = lean_nat_add(v_i_4638_, v___x_4660_);
v___x_4662_ = lean_array_push(v_acc_4642_, v_stx_4643_);
v___x_4663_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4639_, v_a_4640_, v_p_4641_, v___x_4661_, v___x_4662_);
return v___x_4663_;
}
else
{
goto v___jp_4645_;
}
}
}
else
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4664_ = lean_unsigned_to_nat(2u);
v___x_4665_ = lean_nat_add(v_i_4638_, v___x_4664_);
v___x_4666_ = lean_array_push(v_acc_4642_, v_stx_4643_);
v___x_4667_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4639_, v_a_4640_, v_p_4641_, v___x_4665_, v___x_4666_);
return v___x_4667_;
}
}
v___jp_4645_:
{
lean_object* v___x_4646_; lean_object* v_sepStx_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4646_ = lean_nat_pred(v_i_4638_);
v_sepStx_4647_ = lean_array_fget_borrowed(v_a_4640_, v___x_4646_);
lean_dec(v___x_4646_);
v___x_4648_ = lean_unsigned_to_nat(2u);
v___x_4649_ = lean_nat_add(v_i_4638_, v___x_4648_);
lean_inc(v_sepStx_4647_);
v___x_4650_ = lean_array_push(v_acc_4642_, v_sepStx_4647_);
v___x_4651_ = lean_array_push(v___x_4650_, v_stx_4643_);
v___x_4652_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4639_, v_a_4640_, v_p_4641_, v___x_4649_, v___x_4651_);
return v___x_4652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4668_, lean_object* v_inst_4669_, lean_object* v_a_4670_, lean_object* v_p_4671_, lean_object* v_acc_4672_, lean_object* v_stx_4673_, lean_object* v_____do__lift_4674_){
_start:
{
uint8_t v_____do__lift_284__boxed_4675_; lean_object* v_res_4676_; 
v_____do__lift_284__boxed_4675_ = lean_unbox(v_____do__lift_4674_);
v_res_4676_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4668_, v_inst_4669_, v_a_4670_, v_p_4671_, v_acc_4672_, v_stx_4673_, v_____do__lift_284__boxed_4675_);
lean_dec(v_i_4668_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4677_, lean_object* v_a_4678_, lean_object* v_p_4679_, lean_object* v_i_4680_, lean_object* v_acc_4681_){
_start:
{
lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4682_ = lean_array_get_size(v_a_4678_);
v___x_4683_ = lean_nat_dec_lt(v_i_4680_, v___x_4682_);
if (v___x_4683_ == 0)
{
lean_object* v_toApplicative_4684_; lean_object* v_toPure_4685_; lean_object* v___x_4686_; 
lean_dec(v_i_4680_);
lean_dec(v_p_4679_);
lean_dec_ref(v_a_4678_);
v_toApplicative_4684_ = lean_ctor_get(v_inst_4677_, 0);
lean_inc_ref(v_toApplicative_4684_);
lean_dec_ref(v_inst_4677_);
v_toPure_4685_ = lean_ctor_get(v_toApplicative_4684_, 1);
lean_inc(v_toPure_4685_);
lean_dec_ref(v_toApplicative_4684_);
v___x_4686_ = lean_apply_2(v_toPure_4685_, lean_box(0), v_acc_4681_);
return v___x_4686_;
}
else
{
lean_object* v_toBind_4687_; lean_object* v_stx_4688_; lean_object* v___f_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v_toBind_4687_ = lean_ctor_get(v_inst_4677_, 1);
lean_inc(v_toBind_4687_);
v_stx_4688_ = lean_array_fget(v_a_4678_, v_i_4680_);
lean_inc(v_stx_4688_);
lean_inc(v_p_4679_);
v___f_4689_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4689_, 0, v_i_4680_);
lean_closure_set(v___f_4689_, 1, v_inst_4677_);
lean_closure_set(v___f_4689_, 2, v_a_4678_);
lean_closure_set(v___f_4689_, 3, v_p_4679_);
lean_closure_set(v___f_4689_, 4, v_acc_4681_);
lean_closure_set(v___f_4689_, 5, v_stx_4688_);
v___x_4690_ = lean_apply_1(v_p_4679_, v_stx_4688_);
v___x_4691_ = lean_apply_4(v_toBind_4687_, lean_box(0), lean_box(0), v___x_4690_, v___f_4689_);
return v___x_4691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4692_, lean_object* v_inst_4693_, lean_object* v_a_4694_, lean_object* v_p_4695_, lean_object* v_i_4696_, lean_object* v_acc_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4693_, v_a_4694_, v_p_4695_, v_i_4696_, v_acc_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4699_, lean_object* v_a_4700_, lean_object* v_p_4701_){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___x_4703_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4704_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4699_, v_a_4700_, v_p_4701_, v___x_4702_, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4705_, lean_object* v_inst_4706_, lean_object* v_a_4707_, lean_object* v_p_4708_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Array_filterSepElemsM___redArg(v_inst_4706_, v_a_4707_, v_p_4708_);
return v___x_4709_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4710_, lean_object* v_x_4711_){
_start:
{
lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4712_ = lean_apply_1(v_p_4710_, v_x_4711_);
v___x_4713_ = lean_unbox(v___x_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4714_, lean_object* v_x_4715_){
_start:
{
uint8_t v_res_4716_; lean_object* v_r_4717_; 
v_res_4716_ = l_Array_filterSepElems___lam__0(v_p_4714_, v_x_4715_);
v_r_4717_ = lean_box(v_res_4716_);
return v_r_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4718_, lean_object* v_p_4719_, lean_object* v_i_4720_, lean_object* v_acc_4721_){
_start:
{
lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4722_ = lean_array_get_size(v_a_4718_);
v___x_4723_ = lean_nat_dec_lt(v_i_4720_, v___x_4722_);
if (v___x_4723_ == 0)
{
lean_dec(v_i_4720_);
lean_dec_ref(v_p_4719_);
return v_acc_4721_;
}
else
{
lean_object* v_stx_4724_; lean_object* v___x_4733_; uint8_t v___x_4734_; 
v_stx_4724_ = lean_array_fget_borrowed(v_a_4718_, v_i_4720_);
lean_inc_ref(v_p_4719_);
lean_inc(v_stx_4724_);
v___x_4733_ = lean_apply_1(v_p_4719_, v_stx_4724_);
v___x_4734_ = lean_unbox(v___x_4733_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4735_ = lean_unsigned_to_nat(2u);
v___x_4736_ = lean_nat_add(v_i_4720_, v___x_4735_);
lean_dec(v_i_4720_);
v_i_4720_ = v___x_4736_;
goto _start;
}
else
{
lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___x_4738_ = lean_array_get_size(v_acc_4721_);
v___x_4739_ = lean_unsigned_to_nat(0u);
v___x_4740_ = lean_nat_dec_eq(v___x_4738_, v___x_4739_);
if (v___x_4740_ == 0)
{
uint8_t v___x_4741_; 
v___x_4741_ = lean_nat_dec_eq(v_i_4720_, v___x_4739_);
if (v___x_4741_ == 0)
{
goto v___jp_4725_;
}
else
{
if (v___x_4740_ == 0)
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_unsigned_to_nat(2u);
v___x_4743_ = lean_nat_add(v_i_4720_, v___x_4742_);
lean_dec(v_i_4720_);
lean_inc(v_stx_4724_);
v___x_4744_ = lean_array_push(v_acc_4721_, v_stx_4724_);
v_i_4720_ = v___x_4743_;
v_acc_4721_ = v___x_4744_;
goto _start;
}
else
{
goto v___jp_4725_;
}
}
}
else
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = lean_unsigned_to_nat(2u);
v___x_4747_ = lean_nat_add(v_i_4720_, v___x_4746_);
lean_dec(v_i_4720_);
lean_inc(v_stx_4724_);
v___x_4748_ = lean_array_push(v_acc_4721_, v_stx_4724_);
v_i_4720_ = v___x_4747_;
v_acc_4721_ = v___x_4748_;
goto _start;
}
}
v___jp_4725_:
{
lean_object* v___x_4726_; lean_object* v_sepStx_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4726_ = lean_nat_pred(v_i_4720_);
v_sepStx_4727_ = lean_array_fget_borrowed(v_a_4718_, v___x_4726_);
lean_dec(v___x_4726_);
v___x_4728_ = lean_unsigned_to_nat(2u);
v___x_4729_ = lean_nat_add(v_i_4720_, v___x_4728_);
lean_dec(v_i_4720_);
lean_inc(v_sepStx_4727_);
v___x_4730_ = lean_array_push(v_acc_4721_, v_sepStx_4727_);
lean_inc(v_stx_4724_);
v___x_4731_ = lean_array_push(v___x_4730_, v_stx_4724_);
v_i_4720_ = v___x_4729_;
v_acc_4721_ = v___x_4731_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4750_, lean_object* v_p_4751_, lean_object* v_i_4752_, lean_object* v_acc_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4750_, v_p_4751_, v_i_4752_, v_acc_4753_);
lean_dec_ref(v_a_4750_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4755_, lean_object* v_p_4756_){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4759_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4755_, v_p_4756_, v___x_4757_, v___x_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4760_, lean_object* v_p_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4760_, v_p_4761_);
lean_dec_ref(v_a_4760_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4763_, lean_object* v_p_4764_){
_start:
{
lean_object* v___f_4765_; lean_object* v___x_4766_; 
v___f_4765_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4765_, 0, v_p_4764_);
v___x_4766_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4763_, v___f_4765_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4767_, lean_object* v_p_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Array_filterSepElems(v_a_4767_, v_p_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4770_, lean_object* v_acc_4771_, lean_object* v_inst_4772_, lean_object* v_a_4773_, lean_object* v_f_4774_, lean_object* v_stx_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4770_, v_acc_4771_, v_inst_4772_, v_a_4773_, v_f_4774_, v_stx_4775_);
lean_dec(v_i_4770_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4777_, lean_object* v_a_4778_, lean_object* v_f_4779_, lean_object* v_i_4780_, lean_object* v_acc_4781_){
_start:
{
lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4782_ = lean_array_get_size(v_a_4778_);
v___x_4783_ = lean_nat_dec_lt(v_i_4780_, v___x_4782_);
if (v___x_4783_ == 0)
{
lean_object* v_toApplicative_4784_; lean_object* v_toPure_4785_; lean_object* v___x_4786_; 
lean_dec(v_i_4780_);
lean_dec(v_f_4779_);
lean_dec_ref(v_a_4778_);
v_toApplicative_4784_ = lean_ctor_get(v_inst_4777_, 0);
lean_inc_ref(v_toApplicative_4784_);
lean_dec_ref(v_inst_4777_);
v_toPure_4785_ = lean_ctor_get(v_toApplicative_4784_, 1);
lean_inc(v_toPure_4785_);
lean_dec_ref(v_toApplicative_4784_);
v___x_4786_ = lean_apply_2(v_toPure_4785_, lean_box(0), v_acc_4781_);
return v___x_4786_;
}
else
{
lean_object* v_stx_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v_stx_4787_ = lean_array_fget_borrowed(v_a_4778_, v_i_4780_);
v___x_4788_ = lean_unsigned_to_nat(2u);
v___x_4789_ = lean_nat_mod(v_i_4780_, v___x_4788_);
v___x_4790_ = lean_unsigned_to_nat(0u);
v___x_4791_ = lean_nat_dec_eq(v___x_4789_, v___x_4790_);
lean_dec(v___x_4789_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = lean_unsigned_to_nat(1u);
v___x_4793_ = lean_nat_add(v_i_4780_, v___x_4792_);
lean_dec(v_i_4780_);
lean_inc(v_stx_4787_);
v___x_4794_ = lean_array_push(v_acc_4781_, v_stx_4787_);
v_i_4780_ = v___x_4793_;
v_acc_4781_ = v___x_4794_;
goto _start;
}
else
{
lean_object* v_toBind_4796_; lean_object* v___f_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_inc(v_stx_4787_);
v_toBind_4796_ = lean_ctor_get(v_inst_4777_, 1);
lean_inc(v_toBind_4796_);
lean_inc(v_f_4779_);
v___f_4797_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4797_, 0, v_i_4780_);
lean_closure_set(v___f_4797_, 1, v_acc_4781_);
lean_closure_set(v___f_4797_, 2, v_inst_4777_);
lean_closure_set(v___f_4797_, 3, v_a_4778_);
lean_closure_set(v___f_4797_, 4, v_f_4779_);
v___x_4798_ = lean_apply_1(v_f_4779_, v_stx_4787_);
v___x_4799_ = lean_apply_4(v_toBind_4796_, lean_box(0), lean_box(0), v___x_4798_, v___f_4797_);
return v___x_4799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4800_, lean_object* v_acc_4801_, lean_object* v_inst_4802_, lean_object* v_a_4803_, lean_object* v_f_4804_, lean_object* v_stx_4805_){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4806_ = lean_unsigned_to_nat(1u);
v___x_4807_ = lean_nat_add(v_i_4800_, v___x_4806_);
v___x_4808_ = lean_array_push(v_acc_4801_, v_stx_4805_);
v___x_4809_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4802_, v_a_4803_, v_f_4804_, v___x_4807_, v___x_4808_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4810_, lean_object* v_inst_4811_, lean_object* v_a_4812_, lean_object* v_f_4813_, lean_object* v_i_4814_, lean_object* v_acc_4815_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4811_, v_a_4812_, v_f_4813_, v_i_4814_, v_acc_4815_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4817_, lean_object* v_a_4818_, lean_object* v_f_4819_){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4820_ = lean_unsigned_to_nat(0u);
v___x_4821_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4822_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4817_, v_a_4818_, v_f_4819_, v___x_4820_, v___x_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4823_, lean_object* v_inst_4824_, lean_object* v_a_4825_, lean_object* v_f_4826_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Array_mapSepElemsM___redArg(v_inst_4824_, v_a_4825_, v_f_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4828_, lean_object* v_x_4829_){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_apply_1(v_f_4828_, v_x_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4831_, lean_object* v_f_4832_, lean_object* v_i_4833_, lean_object* v_acc_4834_){
_start:
{
lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4835_ = lean_array_get_size(v_a_4831_);
v___x_4836_ = lean_nat_dec_lt(v_i_4833_, v___x_4835_);
if (v___x_4836_ == 0)
{
lean_dec(v_i_4833_);
lean_dec_ref(v_f_4832_);
return v_acc_4834_;
}
else
{
lean_object* v_stx_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; 
v_stx_4837_ = lean_array_fget_borrowed(v_a_4831_, v_i_4833_);
v___x_4838_ = lean_unsigned_to_nat(2u);
v___x_4839_ = lean_nat_mod(v_i_4833_, v___x_4838_);
v___x_4840_ = lean_unsigned_to_nat(0u);
v___x_4841_ = lean_nat_dec_eq(v___x_4839_, v___x_4840_);
lean_dec(v___x_4839_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4842_ = lean_unsigned_to_nat(1u);
v___x_4843_ = lean_nat_add(v_i_4833_, v___x_4842_);
lean_dec(v_i_4833_);
lean_inc(v_stx_4837_);
v___x_4844_ = lean_array_push(v_acc_4834_, v_stx_4837_);
v_i_4833_ = v___x_4843_;
v_acc_4834_ = v___x_4844_;
goto _start;
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_inc_ref(v_f_4832_);
lean_inc(v_stx_4837_);
v___x_4846_ = lean_apply_1(v_f_4832_, v_stx_4837_);
v___x_4847_ = lean_unsigned_to_nat(1u);
v___x_4848_ = lean_nat_add(v_i_4833_, v___x_4847_);
lean_dec(v_i_4833_);
v___x_4849_ = lean_array_push(v_acc_4834_, v___x_4846_);
v_i_4833_ = v___x_4848_;
v_acc_4834_ = v___x_4849_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4851_, lean_object* v_f_4852_, lean_object* v_i_4853_, lean_object* v_acc_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4851_, v_f_4852_, v_i_4853_, v_acc_4854_);
lean_dec_ref(v_a_4851_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4856_, lean_object* v_f_4857_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4858_ = lean_unsigned_to_nat(0u);
v___x_4859_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4860_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4856_, v_f_4857_, v___x_4858_, v___x_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4861_, lean_object* v_f_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4861_, v_f_4862_);
lean_dec_ref(v_a_4861_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4864_, lean_object* v_f_4865_){
_start:
{
lean_object* v___f_4866_; lean_object* v___x_4867_; 
v___f_4866_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4866_, 0, v_f_4865_);
v___x_4867_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4864_, v___f_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4868_, lean_object* v_f_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Array_mapSepElems(v_a_4868_, v_f_4869_);
lean_dec_ref(v_a_4868_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4871_, size_t v_i_4872_, size_t v_stop_4873_, lean_object* v_b_4874_){
_start:
{
lean_object* v___y_4876_; uint8_t v___x_4880_; 
v___x_4880_ = lean_usize_dec_eq(v_i_4872_, v_stop_4873_);
if (v___x_4880_ == 0)
{
lean_object* v_fst_4881_; uint8_t v___x_4882_; 
v_fst_4881_ = lean_ctor_get(v_b_4874_, 0);
v___x_4882_ = lean_unbox(v_fst_4881_);
if (v___x_4882_ == 0)
{
lean_object* v_snd_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4892_; 
v_snd_4883_ = lean_ctor_get(v_b_4874_, 1);
v_isSharedCheck_4892_ = !lean_is_exclusive(v_b_4874_);
if (v_isSharedCheck_4892_ == 0)
{
lean_object* v_unused_4893_; 
v_unused_4893_ = lean_ctor_get(v_b_4874_, 0);
lean_dec(v_unused_4893_);
v___x_4885_ = v_b_4874_;
v_isShared_4886_ = v_isSharedCheck_4892_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_snd_4883_);
lean_dec(v_b_4874_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4892_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
uint8_t v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4887_ = 1;
v___x_4888_ = lean_box(v___x_4887_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v___x_4888_);
v___x_4890_ = v___x_4885_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
lean_ctor_set(v_reuseFailAlloc_4891_, 1, v_snd_4883_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
v___y_4876_ = v___x_4890_;
goto v___jp_4875_;
}
}
}
else
{
lean_object* v_snd_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4904_; 
v_snd_4894_ = lean_ctor_get(v_b_4874_, 1);
v_isSharedCheck_4904_ = !lean_is_exclusive(v_b_4874_);
if (v_isSharedCheck_4904_ == 0)
{
lean_object* v_unused_4905_; 
v_unused_4905_ = lean_ctor_get(v_b_4874_, 0);
lean_dec(v_unused_4905_);
v___x_4896_ = v_b_4874_;
v_isShared_4897_ = v_isSharedCheck_4904_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_snd_4894_);
lean_dec(v_b_4874_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4904_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4902_; 
v___x_4898_ = lean_array_uget_borrowed(v_as_4871_, v_i_4872_);
lean_inc(v___x_4898_);
v___x_4899_ = lean_array_push(v_snd_4894_, v___x_4898_);
v___x_4900_ = lean_box(v___x_4880_);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 1, v___x_4899_);
lean_ctor_set(v___x_4896_, 0, v___x_4900_);
v___x_4902_ = v___x_4896_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v___x_4899_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
v___y_4876_ = v___x_4902_;
goto v___jp_4875_;
}
}
}
}
else
{
return v_b_4874_;
}
v___jp_4875_:
{
size_t v___x_4877_; size_t v___x_4878_; 
v___x_4877_ = ((size_t)1ULL);
v___x_4878_ = lean_usize_add(v_i_4872_, v___x_4877_);
v_i_4872_ = v___x_4878_;
v_b_4874_ = v___y_4876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4906_, lean_object* v_i_4907_, lean_object* v_stop_4908_, lean_object* v_b_4909_){
_start:
{
size_t v_i_boxed_4910_; size_t v_stop_boxed_4911_; lean_object* v_res_4912_; 
v_i_boxed_4910_ = lean_unbox_usize(v_i_4907_);
lean_dec(v_i_4907_);
v_stop_boxed_4911_ = lean_unbox_usize(v_stop_4908_);
lean_dec(v_stop_4908_);
v_res_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4906_, v_i_boxed_4910_, v_stop_boxed_4911_, v_b_4909_);
lean_dec_ref(v_as_4906_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4913_){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; 
v___x_4914_ = lean_unsigned_to_nat(0u);
v___x_4915_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4916_ = lean_array_get_size(v_sa_4913_);
v___x_4917_ = lean_nat_dec_lt(v___x_4914_, v___x_4916_);
if (v___x_4917_ == 0)
{
return v___x_4915_;
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4918_ = lean_box(v___x_4917_);
v___x_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v___x_4915_);
v___x_4920_ = lean_nat_dec_le(v___x_4916_, v___x_4916_);
if (v___x_4920_ == 0)
{
if (v___x_4917_ == 0)
{
lean_dec_ref(v___x_4919_);
return v___x_4915_;
}
else
{
size_t v___x_4921_; size_t v___x_4922_; lean_object* v___x_4923_; lean_object* v_snd_4924_; 
v___x_4921_ = ((size_t)0ULL);
v___x_4922_ = lean_usize_of_nat(v___x_4916_);
v___x_4923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4913_, v___x_4921_, v___x_4922_, v___x_4919_);
v_snd_4924_ = lean_ctor_get(v___x_4923_, 1);
lean_inc(v_snd_4924_);
lean_dec_ref(v___x_4923_);
return v_snd_4924_;
}
}
else
{
size_t v___x_4925_; size_t v___x_4926_; lean_object* v___x_4927_; lean_object* v_snd_4928_; 
v___x_4925_ = ((size_t)0ULL);
v___x_4926_ = lean_usize_of_nat(v___x_4916_);
v___x_4927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4913_, v___x_4925_, v___x_4926_, v___x_4919_);
v_snd_4928_ = lean_ctor_get(v___x_4927_, 1);
lean_inc(v_snd_4928_);
lean_dec_ref(v___x_4927_);
return v_snd_4928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4929_);
lean_dec_ref(v_sa_4929_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4931_, lean_object* v_sa_4932_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4932_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4934_, lean_object* v_sa_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_Syntax_SepArray_getElems(v_sep_4934_, v_sa_4935_);
lean_dec_ref(v_sa_4935_);
lean_dec_ref(v_sep_4934_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4937_){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; uint8_t v___x_4941_; 
v___x_4938_ = lean_unsigned_to_nat(0u);
v___x_4939_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4940_ = lean_array_get_size(v_sa_4937_);
v___x_4941_ = lean_nat_dec_lt(v___x_4938_, v___x_4940_);
if (v___x_4941_ == 0)
{
return v___x_4939_;
}
else
{
lean_object* v___x_4942_; lean_object* v___x_4943_; uint8_t v___x_4944_; 
v___x_4942_ = lean_box(v___x_4941_);
v___x_4943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
lean_ctor_set(v___x_4943_, 1, v___x_4939_);
v___x_4944_ = lean_nat_dec_le(v___x_4940_, v___x_4940_);
if (v___x_4944_ == 0)
{
if (v___x_4941_ == 0)
{
lean_dec_ref(v___x_4943_);
return v___x_4939_;
}
else
{
size_t v___x_4945_; size_t v___x_4946_; lean_object* v___x_4947_; lean_object* v_snd_4948_; 
v___x_4945_ = ((size_t)0ULL);
v___x_4946_ = lean_usize_of_nat(v___x_4940_);
v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4937_, v___x_4945_, v___x_4946_, v___x_4943_);
v_snd_4948_ = lean_ctor_get(v___x_4947_, 1);
lean_inc(v_snd_4948_);
lean_dec_ref(v___x_4947_);
return v_snd_4948_;
}
}
else
{
size_t v___x_4949_; size_t v___x_4950_; lean_object* v___x_4951_; lean_object* v_snd_4952_; 
v___x_4949_ = ((size_t)0ULL);
v___x_4950_ = lean_usize_of_nat(v___x_4940_);
v___x_4951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4937_, v___x_4949_, v___x_4950_, v___x_4943_);
v_snd_4952_ = lean_ctor_get(v___x_4951_, 1);
lean_inc(v_snd_4952_);
lean_dec_ref(v___x_4951_);
return v_snd_4952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4953_);
lean_dec_ref(v_sa_4953_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4955_, lean_object* v_sep_4956_, lean_object* v_sa_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4959_, lean_object* v_sep_4960_, lean_object* v_sa_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_Lean_Syntax_TSepArray_getElems(v_k_4959_, v_sep_4960_, v_sa_4961_);
lean_dec_ref(v_sa_4961_);
lean_dec_ref(v_sep_4960_);
lean_dec(v_k_4959_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4963_, lean_object* v_sa_4964_, lean_object* v_e_4965_){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; uint8_t v___x_4968_; 
v___x_4966_ = lean_array_get_size(v_sa_4964_);
v___x_4967_ = lean_unsigned_to_nat(0u);
v___x_4968_ = lean_nat_dec_eq(v___x_4966_, v___x_4967_);
if (v___x_4968_ == 0)
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4969_ = l_Lean_mkAtom(v_sep_4963_);
v___x_4970_ = lean_array_push(v_sa_4964_, v___x_4969_);
v___x_4971_ = lean_array_push(v___x_4970_, v_e_4965_);
return v___x_4971_;
}
else
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
lean_dec_ref(v_sa_4964_);
lean_dec_ref(v_sep_4963_);
v___x_4972_ = lean_unsigned_to_nat(1u);
v___x_4973_ = lean_mk_empty_array_with_capacity(v___x_4972_);
v___x_4974_ = lean_array_push(v___x_4973_, v_e_4965_);
return v___x_4974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4975_, lean_object* v_sep_4976_, lean_object* v_sa_4977_, lean_object* v_e_4978_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4976_, v_sa_4977_, v_e_4978_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4980_, lean_object* v_sep_4981_, lean_object* v_sa_4982_, lean_object* v_e_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_Syntax_TSepArray_push(v_k_4980_, v_sep_4981_, v_sa_4982_, v_e_4983_);
lean_dec(v_k_4980_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4985_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4987_);
lean_dec_ref(v_sep_4987_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4989_, lean_object* v_k_4990_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4992_, lean_object* v_k_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4992_, v_k_4993_);
lean_dec_ref(v_k_4993_);
lean_dec(v_sep_4992_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object* v_sep_4995_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___boxed), 2, 1);
lean_closure_set(v___x_4996_, 0, v_sep_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4997_, lean_object* v_sep_4998_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4999_, 0, v_k_4997_);
lean_closure_set(v___x_4999_, 1, v_sep_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_5000_, lean_object* v_x_5001_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = lean_apply_1(v_inst_5000_, v_x_5001_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5003_, lean_object* v_a_5004_){
_start:
{
lean_object* v___x_5005_; size_t v_sz_5006_; size_t v___x_5007_; lean_object* v___x_5008_; 
v___x_5005_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5006_ = lean_array_size(v_a_5004_);
v___x_5007_ = ((size_t)0ULL);
v___x_5008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5005_, v___f_5003_, v_sz_5006_, v___x_5007_, v_a_5004_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5009_){
_start:
{
lean_object* v___f_5010_; lean_object* v___f_5011_; 
v___f_5010_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5010_, 0, v_inst_5009_);
v___f_5011_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5011_, 0, v___f_5010_);
return v___f_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5012_, lean_object* v_k_x27_5013_, lean_object* v_inst_5014_){
_start:
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5014_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5016_, lean_object* v_k_x27_5017_, lean_object* v_inst_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5016_, v_k_x27_5017_, v_inst_5018_);
lean_dec(v_k_x27_5017_);
lean_dec(v_k_5016_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object* v_a_5020_){
_start:
{
lean_inc_ref(v_a_5020_);
return v_a_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(v_a_5021_);
lean_dec_ref(v_a_5021_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5024_){
_start:
{
lean_object* v___f_5025_; 
v___f_5025_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0));
return v___f_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5026_);
lean_dec(v_k_5026_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5035_){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5036_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_5037_ = lean_box(2);
v___x_5038_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5039_ = lean_unsigned_to_nat(2u);
v___x_5040_ = lean_mk_empty_array_with_capacity(v___x_5039_);
v___x_5041_ = lean_array_push(v___x_5040_, v_id_5035_);
v___x_5042_ = lean_array_push(v___x_5041_, v___x_5038_);
v___x_5043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5037_);
lean_ctor_set(v___x_5043_, 1, v___x_5036_);
lean_ctor_set(v___x_5043_, 2, v___x_5042_);
return v___x_5043_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = 123;
v___x_5048_ = lean_box_uint32(v___x_5047_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5049_, lean_object* v_i_5050_){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l_Lean_Syntax_decodeQuotedChar(v_s_5049_, v_i_5050_);
if (lean_obj_tag(v___x_5051_) == 0)
{
uint32_t v_c_5052_; uint32_t v___x_5053_; uint8_t v___x_5054_; 
v_c_5052_ = lean_string_utf8_get(v_s_5049_, v_i_5050_);
v___x_5053_ = 123;
v___x_5054_ = lean_uint32_dec_eq(v_c_5052_, v___x_5053_);
if (v___x_5054_ == 0)
{
return v___x_5051_;
}
else
{
lean_object* v_i_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v_i_5055_ = lean_string_utf8_next(v_s_5049_, v_i_5050_);
v___x_5056_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
lean_ctor_set(v___x_5057_, 1, v_i_5055_);
v___x_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
return v___x_5058_;
}
}
else
{
return v___x_5051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5059_, lean_object* v_i_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5059_, v_i_5060_);
lean_dec(v_i_5060_);
lean_dec_ref(v_s_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5062_, lean_object* v_i_5063_, lean_object* v_acc_5064_){
_start:
{
uint32_t v_c_5065_; lean_object* v_i_5066_; uint8_t v___y_5068_; uint32_t v___x_5087_; uint8_t v___x_5088_; 
v_c_5065_ = lean_string_utf8_get(v_s_5062_, v_i_5063_);
v_i_5066_ = lean_string_utf8_next(v_s_5062_, v_i_5063_);
lean_dec(v_i_5063_);
v___x_5087_ = 34;
v___x_5088_ = lean_uint32_dec_eq(v_c_5065_, v___x_5087_);
if (v___x_5088_ == 0)
{
uint32_t v___x_5089_; uint8_t v___x_5090_; 
v___x_5089_ = 123;
v___x_5090_ = lean_uint32_dec_eq(v_c_5065_, v___x_5089_);
v___y_5068_ = v___x_5090_;
goto v___jp_5067_;
}
else
{
v___y_5068_ = v___x_5088_;
goto v___jp_5067_;
}
v___jp_5067_:
{
if (v___y_5068_ == 0)
{
uint8_t v___x_5069_; 
v___x_5069_ = lean_string_utf8_at_end(v_s_5062_, v_i_5066_);
if (v___x_5069_ == 0)
{
uint32_t v___x_5070_; uint8_t v___x_5071_; 
v___x_5070_ = 92;
v___x_5071_ = lean_uint32_dec_eq(v_c_5065_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; 
v___x_5072_ = lean_string_push(v_acc_5064_, v_c_5065_);
v_i_5063_ = v_i_5066_;
v_acc_5064_ = v___x_5072_;
goto _start;
}
else
{
lean_object* v___x_5074_; 
v___x_5074_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5062_, v_i_5066_);
if (lean_obj_tag(v___x_5074_) == 1)
{
lean_object* v_val_5075_; lean_object* v_fst_5076_; lean_object* v_snd_5077_; uint32_t v___x_5078_; lean_object* v___x_5079_; 
lean_dec(v_i_5066_);
v_val_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_val_5075_);
lean_dec_ref(v___x_5074_);
v_fst_5076_ = lean_ctor_get(v_val_5075_, 0);
lean_inc(v_fst_5076_);
v_snd_5077_ = lean_ctor_get(v_val_5075_, 1);
lean_inc(v_snd_5077_);
lean_dec(v_val_5075_);
v___x_5078_ = lean_unbox_uint32(v_fst_5076_);
lean_dec(v_fst_5076_);
v___x_5079_ = lean_string_push(v_acc_5064_, v___x_5078_);
v_i_5063_ = v_snd_5077_;
v_acc_5064_ = v___x_5079_;
goto _start;
}
else
{
lean_object* v___x_5081_; 
lean_dec(v___x_5074_);
lean_inc_ref(v_s_5062_);
v___x_5081_ = l_Lean_Syntax_decodeStringGap(v_s_5062_, v_i_5066_);
lean_dec(v_i_5066_);
if (lean_obj_tag(v___x_5081_) == 1)
{
lean_object* v_val_5082_; 
v_val_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_val_5082_);
lean_dec_ref(v___x_5081_);
v_i_5063_ = v_val_5082_;
goto _start;
}
else
{
lean_object* v___x_5084_; 
lean_dec(v___x_5081_);
lean_dec_ref(v_acc_5064_);
lean_dec_ref(v_s_5062_);
v___x_5084_ = lean_box(0);
return v___x_5084_;
}
}
}
}
else
{
lean_object* v___x_5085_; 
lean_dec(v_i_5066_);
lean_dec_ref(v_acc_5064_);
lean_dec_ref(v_s_5062_);
v___x_5085_ = lean_box(0);
return v___x_5085_;
}
}
else
{
lean_object* v___x_5086_; 
lean_dec(v_i_5066_);
lean_dec_ref(v_s_5062_);
v___x_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5086_, 0, v_acc_5064_);
return v___x_5086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5091_){
_start:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5092_ = lean_unsigned_to_nat(1u);
v___x_5093_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5094_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5091_, v___x_5092_, v___x_5093_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5098_){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5100_ = l_Lean_Syntax_isLit_x3f(v___x_5099_, v_stx_5098_);
if (lean_obj_tag(v___x_5100_) == 0)
{
return v___x_5100_;
}
else
{
lean_object* v_val_5101_; lean_object* v___x_5102_; 
v_val_5101_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_val_5101_);
lean_dec_ref(v___x_5100_);
v___x_5102_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5101_);
return v___x_5102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5103_);
lean_dec(v_stx_5103_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5105_){
_start:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; 
v___x_5106_ = l_Lean_Syntax_getArgs(v_stx_5105_);
v___x_5107_ = lean_unsigned_to_nat(0u);
v___x_5108_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5109_ = lean_array_get_size(v___x_5106_);
v___x_5110_ = lean_nat_dec_lt(v___x_5107_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_dec_ref(v___x_5106_);
return v___x_5108_;
}
else
{
lean_object* v___x_5111_; lean_object* v___x_5112_; uint8_t v___x_5113_; 
v___x_5111_ = lean_box(v___x_5110_);
v___x_5112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5111_);
lean_ctor_set(v___x_5112_, 1, v___x_5108_);
v___x_5113_ = lean_nat_dec_le(v___x_5109_, v___x_5109_);
if (v___x_5113_ == 0)
{
if (v___x_5110_ == 0)
{
lean_dec_ref(v___x_5112_);
lean_dec_ref(v___x_5106_);
return v___x_5108_;
}
else
{
size_t v___x_5114_; size_t v___x_5115_; lean_object* v___x_5116_; lean_object* v_snd_5117_; 
v___x_5114_ = ((size_t)0ULL);
v___x_5115_ = lean_usize_of_nat(v___x_5109_);
v___x_5116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5106_, v___x_5114_, v___x_5115_, v___x_5112_);
lean_dec_ref(v___x_5106_);
v_snd_5117_ = lean_ctor_get(v___x_5116_, 1);
lean_inc(v_snd_5117_);
lean_dec_ref(v___x_5116_);
return v_snd_5117_;
}
}
else
{
size_t v___x_5118_; size_t v___x_5119_; lean_object* v___x_5120_; lean_object* v_snd_5121_; 
v___x_5118_ = ((size_t)0ULL);
v___x_5119_ = lean_usize_of_nat(v___x_5109_);
v___x_5120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5106_, v___x_5118_, v___x_5119_, v___x_5112_);
lean_dec_ref(v___x_5106_);
v_snd_5121_ = lean_ctor_get(v___x_5120_, 1);
lean_inc(v_snd_5121_);
lean_dec_ref(v___x_5120_);
return v_snd_5121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_Syntax_getSepArgs(v_stx_5122_);
lean_dec(v_stx_5122_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5124_, lean_object* v_mkElem_5125_, lean_object* v_mkLit_5126_, lean_object* v_as_5127_, size_t v_sz_5128_, size_t v_i_5129_, lean_object* v_b_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_a_5134_; lean_object* v_a_5135_; lean_object* v_elem_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; uint8_t v___x_5147_; 
v___x_5147_ = lean_usize_dec_lt(v_i_5129_, v_sz_5128_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; 
lean_dec_ref(v___y_5131_);
lean_dec_ref(v_mkLit_5126_);
lean_dec_ref(v_mkElem_5125_);
lean_dec_ref(v_mkAppend_5124_);
v___x_5148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5148_, 0, v_b_5130_);
lean_ctor_set(v___x_5148_, 1, v___y_5132_);
return v___x_5148_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5150_; 
v_a_5149_ = lean_array_uget_borrowed(v_as_5127_, v_i_5129_);
v___x_5150_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5149_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_methods_5151_; lean_object* v_quotContext_5152_; lean_object* v_currMacroScope_5153_; lean_object* v_currRecDepth_5154_; lean_object* v_maxRecDepth_5155_; lean_object* v_ref_5156_; lean_object* v_ref_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; 
v_methods_5151_ = lean_ctor_get(v___y_5131_, 0);
v_quotContext_5152_ = lean_ctor_get(v___y_5131_, 1);
v_currMacroScope_5153_ = lean_ctor_get(v___y_5131_, 2);
v_currRecDepth_5154_ = lean_ctor_get(v___y_5131_, 3);
v_maxRecDepth_5155_ = lean_ctor_get(v___y_5131_, 4);
v_ref_5156_ = lean_ctor_get(v___y_5131_, 5);
v_ref_5157_ = l_Lean_replaceRef(v_a_5149_, v_ref_5156_);
lean_inc(v_maxRecDepth_5155_);
lean_inc(v_currRecDepth_5154_);
lean_inc(v_currMacroScope_5153_);
lean_inc(v_quotContext_5152_);
lean_inc(v_methods_5151_);
v___x_5158_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5158_, 0, v_methods_5151_);
lean_ctor_set(v___x_5158_, 1, v_quotContext_5152_);
lean_ctor_set(v___x_5158_, 2, v_currMacroScope_5153_);
lean_ctor_set(v___x_5158_, 3, v_currRecDepth_5154_);
lean_ctor_set(v___x_5158_, 4, v_maxRecDepth_5155_);
lean_ctor_set(v___x_5158_, 5, v_ref_5157_);
lean_inc_ref(v_mkElem_5125_);
lean_inc(v_a_5149_);
v___x_5159_ = lean_apply_3(v_mkElem_5125_, v_a_5149_, v___x_5158_, v___y_5132_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v_a_5161_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
v_a_5161_ = lean_ctor_get(v___x_5159_, 1);
lean_inc(v_a_5161_);
lean_dec_ref(v___x_5159_);
lean_inc_ref(v___y_5131_);
v_elem_5140_ = v_a_5160_;
v___y_5141_ = v___y_5131_;
v___y_5142_ = v_a_5161_;
goto v___jp_5139_;
}
else
{
lean_dec_ref(v___y_5131_);
lean_dec(v_b_5130_);
lean_dec_ref(v_mkLit_5126_);
lean_dec_ref(v_mkElem_5125_);
lean_dec_ref(v_mkAppend_5124_);
return v___x_5159_;
}
}
else
{
lean_object* v_val_5162_; uint8_t v___x_5163_; 
v_val_5162_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_val_5162_);
lean_dec_ref(v___x_5150_);
lean_inc(v_val_5162_);
v___x_5163_ = lean_string_isempty(v_val_5162_);
if (v___x_5163_ == 0)
{
lean_object* v_methods_5164_; lean_object* v_quotContext_5165_; lean_object* v_currMacroScope_5166_; lean_object* v_currRecDepth_5167_; lean_object* v_maxRecDepth_5168_; lean_object* v_ref_5169_; lean_object* v_ref_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v_methods_5164_ = lean_ctor_get(v___y_5131_, 0);
v_quotContext_5165_ = lean_ctor_get(v___y_5131_, 1);
v_currMacroScope_5166_ = lean_ctor_get(v___y_5131_, 2);
v_currRecDepth_5167_ = lean_ctor_get(v___y_5131_, 3);
v_maxRecDepth_5168_ = lean_ctor_get(v___y_5131_, 4);
v_ref_5169_ = lean_ctor_get(v___y_5131_, 5);
v_ref_5170_ = l_Lean_replaceRef(v_a_5149_, v_ref_5169_);
lean_inc(v_maxRecDepth_5168_);
lean_inc(v_currRecDepth_5167_);
lean_inc(v_currMacroScope_5166_);
lean_inc(v_quotContext_5165_);
lean_inc(v_methods_5164_);
v___x_5171_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5171_, 0, v_methods_5164_);
lean_ctor_set(v___x_5171_, 1, v_quotContext_5165_);
lean_ctor_set(v___x_5171_, 2, v_currMacroScope_5166_);
lean_ctor_set(v___x_5171_, 3, v_currRecDepth_5167_);
lean_ctor_set(v___x_5171_, 4, v_maxRecDepth_5168_);
lean_ctor_set(v___x_5171_, 5, v_ref_5170_);
lean_inc_ref(v_mkLit_5126_);
v___x_5172_ = lean_apply_3(v_mkLit_5126_, v_val_5162_, v___x_5171_, v___y_5132_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v_a_5174_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
v_a_5174_ = lean_ctor_get(v___x_5172_, 1);
lean_inc(v_a_5174_);
lean_dec_ref(v___x_5172_);
lean_inc_ref(v___y_5131_);
v_elem_5140_ = v_a_5173_;
v___y_5141_ = v___y_5131_;
v___y_5142_ = v_a_5174_;
goto v___jp_5139_;
}
else
{
lean_dec_ref(v___y_5131_);
lean_dec(v_b_5130_);
lean_dec_ref(v_mkLit_5126_);
lean_dec_ref(v_mkElem_5125_);
lean_dec_ref(v_mkAppend_5124_);
return v___x_5172_;
}
}
else
{
lean_dec(v_val_5162_);
v_a_5134_ = v_b_5130_;
v_a_5135_ = v___y_5132_;
goto v___jp_5133_;
}
}
}
v___jp_5133_:
{
size_t v___x_5136_; size_t v___x_5137_; 
v___x_5136_ = ((size_t)1ULL);
v___x_5137_ = lean_usize_add(v_i_5129_, v___x_5136_);
v_i_5129_ = v___x_5137_;
v_b_5130_ = v_a_5134_;
v___y_5132_ = v_a_5135_;
goto _start;
}
v___jp_5139_:
{
uint8_t v___x_5143_; 
v___x_5143_ = l_Lean_Syntax_isMissing(v_b_5130_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
lean_inc_ref(v_mkAppend_5124_);
v___x_5144_ = lean_apply_4(v_mkAppend_5124_, v_b_5130_, v_elem_5140_, v___y_5141_, v___y_5142_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v_a_5146_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
v_a_5146_ = lean_ctor_get(v___x_5144_, 1);
lean_inc(v_a_5146_);
lean_dec_ref(v___x_5144_);
v_a_5134_ = v_a_5145_;
v_a_5135_ = v_a_5146_;
goto v___jp_5133_;
}
else
{
lean_dec_ref(v___y_5131_);
lean_dec_ref(v_mkLit_5126_);
lean_dec_ref(v_mkElem_5125_);
lean_dec_ref(v_mkAppend_5124_);
return v___x_5144_;
}
}
else
{
lean_dec_ref(v___y_5141_);
lean_dec(v_b_5130_);
v_a_5134_ = v_elem_5140_;
v_a_5135_ = v___y_5142_;
goto v___jp_5133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5175_, lean_object* v_mkElem_5176_, lean_object* v_mkLit_5177_, lean_object* v_as_5178_, lean_object* v_sz_5179_, lean_object* v_i_5180_, lean_object* v_b_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
size_t v_sz_boxed_5184_; size_t v_i_boxed_5185_; lean_object* v_res_5186_; 
v_sz_boxed_5184_ = lean_unbox_usize(v_sz_5179_);
lean_dec(v_sz_5179_);
v_i_boxed_5185_ = lean_unbox_usize(v_i_5180_);
lean_dec(v_i_5180_);
v_res_5186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5175_, v_mkElem_5176_, v_mkLit_5177_, v_as_5178_, v_sz_boxed_5184_, v_i_boxed_5185_, v_b_5181_, v___y_5182_, v___y_5183_);
lean_dec_ref(v_as_5178_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5187_, lean_object* v_mkAppend_5188_, lean_object* v_mkElem_5189_, lean_object* v_mkLit_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v_result_5193_; size_t v_sz_5194_; size_t v___x_5195_; lean_object* v___x_5196_; 
v_result_5193_ = lean_box(0);
v_sz_5194_ = lean_array_size(v_chunks_5187_);
v___x_5195_ = ((size_t)0ULL);
lean_inc_ref(v_a_5191_);
lean_inc_ref(v_mkLit_5190_);
v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5188_, v_mkElem_5189_, v_mkLit_5190_, v_chunks_5187_, v_sz_5194_, v___x_5195_, v_result_5193_, v_a_5191_, v_a_5192_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; lean_object* v_a_5198_; uint8_t v___x_5199_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_a_5197_);
v_a_5198_ = lean_ctor_get(v___x_5196_, 1);
lean_inc(v_a_5198_);
v___x_5199_ = l_Lean_Syntax_isMissing(v_a_5197_);
lean_dec(v_a_5197_);
if (v___x_5199_ == 0)
{
lean_dec(v_a_5198_);
lean_dec_ref(v_a_5191_);
lean_dec_ref(v_mkLit_5190_);
return v___x_5196_;
}
else
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
lean_dec_ref(v___x_5196_);
v___x_5200_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5201_ = lean_apply_3(v_mkLit_5190_, v___x_5200_, v_a_5191_, v_a_5198_);
return v___x_5201_;
}
}
else
{
lean_dec_ref(v_a_5191_);
lean_dec_ref(v_mkLit_5190_);
return v___x_5196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5202_, lean_object* v_mkAppend_5203_, lean_object* v_mkElem_5204_, lean_object* v_mkLit_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5202_, v_mkAppend_5203_, v_mkElem_5204_, v_mkLit_5205_, v_a_5206_, v_a_5207_);
lean_dec_ref(v_chunks_5202_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5213_, lean_object* v_b_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_ref_5217_; uint8_t v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
v_ref_5217_ = lean_ctor_get(v___y_5215_, 5);
v___x_5218_ = 0;
v___x_5219_ = l_Lean_SourceInfo_fromRef(v_ref_5217_, v___x_5218_);
v___x_5220_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5221_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5219_);
v___x_5222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5219_);
lean_ctor_set(v___x_5222_, 1, v___x_5221_);
v___x_5223_ = l_Lean_Syntax_node3(v___x_5219_, v___x_5220_, v_a_5213_, v___x_5222_, v_b_5214_);
v___x_5224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5223_);
lean_ctor_set(v___x_5224_, 1, v___y_5216_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5225_, lean_object* v_b_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5225_, v_b_5226_, v___y_5227_, v___y_5228_);
lean_dec_ref(v___y_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5230_, lean_object* v_a_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_ref_5234_; uint8_t v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; 
v_ref_5234_ = lean_ctor_get(v___y_5232_, 5);
v___x_5235_ = 0;
v___x_5236_ = l_Lean_SourceInfo_fromRef(v_ref_5234_, v___x_5235_);
v___x_5237_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5238_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5236_);
v___x_5239_ = l_Lean_Syntax_node1(v___x_5236_, v___x_5238_, v_a_5231_);
v___x_5240_ = l_Lean_Syntax_node2(v___x_5236_, v___x_5237_, v_ofInterpFn_5230_, v___x_5239_);
v___x_5241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5240_);
lean_ctor_set(v___x_5241_, 1, v___y_5233_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5242_, lean_object* v_a_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5242_, v_a_5243_, v___y_5244_, v___y_5245_);
lean_dec_ref(v___y_5244_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5247_, lean_object* v_s_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_ref_5251_; uint8_t v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v_ref_5251_ = lean_ctor_get(v___y_5249_, 5);
v___x_5252_ = 0;
v___x_5253_ = l_Lean_SourceInfo_fromRef(v_ref_5251_, v___x_5252_);
v___x_5254_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5255_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5256_ = lean_box(2);
v___x_5257_ = l_Lean_Syntax_mkStrLit(v_s_5248_, v___x_5256_);
lean_inc(v___x_5253_);
v___x_5258_ = l_Lean_Syntax_node1(v___x_5253_, v___x_5255_, v___x_5257_);
v___x_5259_ = l_Lean_Syntax_node2(v___x_5253_, v___x_5254_, v_ofLitFn_5247_, v___x_5258_);
v___x_5260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
lean_ctor_set(v___x_5260_, 1, v___y_5250_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5261_, lean_object* v_s_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5261_, v_s_5262_, v___y_5263_, v___y_5264_);
lean_dec_ref(v___y_5263_);
return v_res_5265_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5283_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5284_ = l_String_toRawSubstring_x27(v___x_5283_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5305_, lean_object* v_type_5306_, lean_object* v_ofInterpFn_5307_, lean_object* v_ofLitFn_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_){
_start:
{
lean_object* v___f_5311_; lean_object* v___f_5312_; lean_object* v___f_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___f_5311_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5312_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5312_, 0, v_ofInterpFn_5307_);
v___f_5313_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5313_, 0, v_ofLitFn_5308_);
v___x_5314_ = l_Lean_Syntax_getArgs(v_interpStr_5305_);
lean_inc_ref(v_a_5309_);
v___x_5315_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5314_, v___f_5311_, v___f_5312_, v___f_5313_, v_a_5309_, v_a_5310_);
lean_dec_ref(v___x_5314_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5348_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
v_a_5317_ = lean_ctor_get(v___x_5315_, 1);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5319_ = v___x_5315_;
v_isShared_5320_ = v_isSharedCheck_5348_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_inc(v_a_5316_);
lean_dec(v___x_5315_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5348_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v_quotContext_5321_; lean_object* v_currMacroScope_5322_; lean_object* v_ref_5323_; uint8_t v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5346_; 
v_quotContext_5321_ = lean_ctor_get(v_a_5309_, 1);
lean_inc(v_quotContext_5321_);
v_currMacroScope_5322_ = lean_ctor_get(v_a_5309_, 2);
lean_inc(v_currMacroScope_5322_);
v_ref_5323_ = lean_ctor_get(v_a_5309_, 5);
lean_inc(v_ref_5323_);
lean_dec_ref(v_a_5309_);
v___x_5324_ = 0;
v___x_5325_ = l_Lean_SourceInfo_fromRef(v_ref_5323_, v___x_5324_);
lean_dec(v_ref_5323_);
v___x_5326_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5327_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5328_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc(v___x_5325_);
v___x_5329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5325_);
lean_ctor_set(v___x_5329_, 1, v___x_5328_);
v___x_5330_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5331_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5332_ = lean_box(0);
v___x_5333_ = l_Lean_addMacroScope(v_quotContext_5321_, v___x_5332_, v_currMacroScope_5322_);
v___x_5334_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
lean_inc(v___x_5325_);
v___x_5335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5335_, 0, v___x_5325_);
lean_ctor_set(v___x_5335_, 1, v___x_5331_);
lean_ctor_set(v___x_5335_, 2, v___x_5333_);
lean_ctor_set(v___x_5335_, 3, v___x_5334_);
lean_inc(v___x_5325_);
v___x_5336_ = l_Lean_Syntax_node1(v___x_5325_, v___x_5330_, v___x_5335_);
lean_inc(v___x_5325_);
v___x_5337_ = l_Lean_Syntax_node2(v___x_5325_, v___x_5327_, v___x_5329_, v___x_5336_);
v___x_5338_ = ((lean_object*)(l_Lean_toolchain___closed__0));
lean_inc(v___x_5325_);
v___x_5339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5325_);
lean_ctor_set(v___x_5339_, 1, v___x_5338_);
v___x_5340_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5325_);
v___x_5341_ = l_Lean_Syntax_node1(v___x_5325_, v___x_5340_, v_type_5306_);
v___x_5342_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
lean_inc(v___x_5325_);
v___x_5343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5325_);
lean_ctor_set(v___x_5343_, 1, v___x_5342_);
v___x_5344_ = l_Lean_Syntax_node5(v___x_5325_, v___x_5326_, v___x_5337_, v_a_5316_, v___x_5339_, v___x_5341_, v___x_5343_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5344_);
v___x_5346_ = v___x_5319_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5347_, 1, v_a_5317_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
lean_dec_ref(v_a_5309_);
lean_dec(v_type_5306_);
v_a_5349_ = lean_ctor_get(v___x_5315_, 0);
v_a_5350_ = lean_ctor_get(v___x_5315_, 1);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5315_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
lean_dec(v___x_5315_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5349_);
lean_ctor_set(v_reuseFailAlloc_5356_, 1, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5358_, lean_object* v_type_5359_, lean_object* v_ofInterpFn_5360_, lean_object* v_ofLitFn_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5358_, v_type_5359_, v_ofInterpFn_5360_, v_ofLitFn_5361_, v_a_5362_, v_a_5363_);
lean_dec(v_interpStr_5358_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5365_){
_start:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; 
v___x_5366_ = lean_unsigned_to_nat(1u);
v___x_5367_ = l_Lean_Syntax_getArg(v_stx_5365_, v___x_5366_);
if (lean_obj_tag(v___x_5367_) == 2)
{
lean_object* v_val_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v_val_5368_ = lean_ctor_get(v___x_5367_, 1);
lean_inc_ref(v_val_5368_);
lean_dec_ref(v___x_5367_);
v___x_5369_ = lean_unsigned_to_nat(0u);
v___x_5370_ = lean_string_utf8_byte_size(v_val_5368_);
v___x_5371_ = lean_unsigned_to_nat(2u);
v___x_5372_ = lean_string_pos_sub(v___x_5370_, v___x_5371_);
v___x_5373_ = lean_string_utf8_extract(v_val_5368_, v___x_5369_, v___x_5372_);
lean_dec(v___x_5372_);
lean_dec_ref(v_val_5368_);
return v___x_5373_;
}
else
{
lean_object* v___x_5374_; 
lean_dec(v___x_5367_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5392_, lean_object* v_prec_5393_){
_start:
{
lean_object* v___y_5395_; lean_object* v___y_5402_; lean_object* v___y_5409_; lean_object* v___y_5416_; lean_object* v___y_5423_; 
switch(v_x_5392_)
{
case 0:
{
lean_object* v___x_5429_; uint8_t v___x_5430_; 
v___x_5429_ = lean_unsigned_to_nat(1024u);
v___x_5430_ = lean_nat_dec_le(v___x_5429_, v_prec_5393_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; 
v___x_5431_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5395_ = v___x_5431_;
goto v___jp_5394_;
}
else
{
lean_object* v___x_5432_; 
v___x_5432_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5395_ = v___x_5432_;
goto v___jp_5394_;
}
}
case 1:
{
lean_object* v___x_5433_; uint8_t v___x_5434_; 
v___x_5433_ = lean_unsigned_to_nat(1024u);
v___x_5434_ = lean_nat_dec_le(v___x_5433_, v_prec_5393_);
if (v___x_5434_ == 0)
{
lean_object* v___x_5435_; 
v___x_5435_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5402_ = v___x_5435_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5436_; 
v___x_5436_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5402_ = v___x_5436_;
goto v___jp_5401_;
}
}
case 2:
{
lean_object* v___x_5437_; uint8_t v___x_5438_; 
v___x_5437_ = lean_unsigned_to_nat(1024u);
v___x_5438_ = lean_nat_dec_le(v___x_5437_, v_prec_5393_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; 
v___x_5439_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5409_ = v___x_5439_;
goto v___jp_5408_;
}
else
{
lean_object* v___x_5440_; 
v___x_5440_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5409_ = v___x_5440_;
goto v___jp_5408_;
}
}
case 3:
{
lean_object* v___x_5441_; uint8_t v___x_5442_; 
v___x_5441_ = lean_unsigned_to_nat(1024u);
v___x_5442_ = lean_nat_dec_le(v___x_5441_, v_prec_5393_);
if (v___x_5442_ == 0)
{
lean_object* v___x_5443_; 
v___x_5443_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5416_ = v___x_5443_;
goto v___jp_5415_;
}
else
{
lean_object* v___x_5444_; 
v___x_5444_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5416_ = v___x_5444_;
goto v___jp_5415_;
}
}
default: 
{
lean_object* v___x_5445_; uint8_t v___x_5446_; 
v___x_5445_ = lean_unsigned_to_nat(1024u);
v___x_5446_ = lean_nat_dec_le(v___x_5445_, v_prec_5393_);
if (v___x_5446_ == 0)
{
lean_object* v___x_5447_; 
v___x_5447_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5423_ = v___x_5447_;
goto v___jp_5422_;
}
else
{
lean_object* v___x_5448_; 
v___x_5448_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5423_ = v___x_5448_;
goto v___jp_5422_;
}
}
}
v___jp_5394_:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; uint8_t v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5396_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
v___x_5397_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5397_, 0, v___y_5395_);
lean_ctor_set(v___x_5397_, 1, v___x_5396_);
v___x_5398_ = 0;
v___x_5399_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5399_, 0, v___x_5397_);
lean_ctor_set_uint8(v___x_5399_, sizeof(void*)*1, v___x_5398_);
v___x_5400_ = l_Repr_addAppParen(v___x_5399_, v_prec_5393_);
return v___x_5400_;
}
v___jp_5401_:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5403_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
v___x_5404_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5404_, 0, v___y_5402_);
lean_ctor_set(v___x_5404_, 1, v___x_5403_);
v___x_5405_ = 0;
v___x_5406_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5406_, 0, v___x_5404_);
lean_ctor_set_uint8(v___x_5406_, sizeof(void*)*1, v___x_5405_);
v___x_5407_ = l_Repr_addAppParen(v___x_5406_, v_prec_5393_);
return v___x_5407_;
}
v___jp_5408_:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; uint8_t v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5410_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
v___x_5411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___y_5409_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = 0;
v___x_5413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5413_, 0, v___x_5411_);
lean_ctor_set_uint8(v___x_5413_, sizeof(void*)*1, v___x_5412_);
v___x_5414_ = l_Repr_addAppParen(v___x_5413_, v_prec_5393_);
return v___x_5414_;
}
v___jp_5415_:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5417_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
v___x_5418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___y_5416_);
lean_ctor_set(v___x_5418_, 1, v___x_5417_);
v___x_5419_ = 0;
v___x_5420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5420_, 0, v___x_5418_);
lean_ctor_set_uint8(v___x_5420_, sizeof(void*)*1, v___x_5419_);
v___x_5421_ = l_Repr_addAppParen(v___x_5420_, v_prec_5393_);
return v___x_5421_;
}
v___jp_5422_:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; uint8_t v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5424_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
v___x_5425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5425_, 0, v___y_5423_);
lean_ctor_set(v___x_5425_, 1, v___x_5424_);
v___x_5426_ = 0;
v___x_5427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5427_, 0, v___x_5425_);
lean_ctor_set_uint8(v___x_5427_, sizeof(void*)*1, v___x_5426_);
v___x_5428_ = l_Repr_addAppParen(v___x_5427_, v_prec_5393_);
return v___x_5428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5449_, lean_object* v_prec_5450_){
_start:
{
uint8_t v_x_285__boxed_5451_; lean_object* v_res_5452_; 
v_x_285__boxed_5451_ = lean_unbox(v_x_5449_);
v_res_5452_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_285__boxed_5451_, v_prec_5450_);
lean_dec(v_prec_5450_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5464_, lean_object* v_prec_5465_){
_start:
{
lean_object* v___y_5467_; lean_object* v___y_5474_; lean_object* v___y_5481_; 
switch(v_x_5464_)
{
case 0:
{
lean_object* v___x_5487_; uint8_t v___x_5488_; 
v___x_5487_ = lean_unsigned_to_nat(1024u);
v___x_5488_ = lean_nat_dec_le(v___x_5487_, v_prec_5465_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5467_ = v___x_5489_;
goto v___jp_5466_;
}
else
{
lean_object* v___x_5490_; 
v___x_5490_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5467_ = v___x_5490_;
goto v___jp_5466_;
}
}
case 1:
{
lean_object* v___x_5491_; uint8_t v___x_5492_; 
v___x_5491_ = lean_unsigned_to_nat(1024u);
v___x_5492_ = lean_nat_dec_le(v___x_5491_, v_prec_5465_);
if (v___x_5492_ == 0)
{
lean_object* v___x_5493_; 
v___x_5493_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5474_ = v___x_5493_;
goto v___jp_5473_;
}
else
{
lean_object* v___x_5494_; 
v___x_5494_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5474_ = v___x_5494_;
goto v___jp_5473_;
}
}
default: 
{
lean_object* v___x_5495_; uint8_t v___x_5496_; 
v___x_5495_ = lean_unsigned_to_nat(1024u);
v___x_5496_ = lean_nat_dec_le(v___x_5495_, v_prec_5465_);
if (v___x_5496_ == 0)
{
lean_object* v___x_5497_; 
v___x_5497_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5481_ = v___x_5497_;
goto v___jp_5480_;
}
else
{
lean_object* v___x_5498_; 
v___x_5498_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5481_ = v___x_5498_;
goto v___jp_5480_;
}
}
}
v___jp_5466_:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5468_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
v___x_5469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5469_, 0, v___y_5467_);
lean_ctor_set(v___x_5469_, 1, v___x_5468_);
v___x_5470_ = 0;
v___x_5471_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5471_, 0, v___x_5469_);
lean_ctor_set_uint8(v___x_5471_, sizeof(void*)*1, v___x_5470_);
v___x_5472_ = l_Repr_addAppParen(v___x_5471_, v_prec_5465_);
return v___x_5472_;
}
v___jp_5473_:
{
lean_object* v___x_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; 
v___x_5475_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
v___x_5476_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5476_, 0, v___y_5474_);
lean_ctor_set(v___x_5476_, 1, v___x_5475_);
v___x_5477_ = 0;
v___x_5478_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5478_, 0, v___x_5476_);
lean_ctor_set_uint8(v___x_5478_, sizeof(void*)*1, v___x_5477_);
v___x_5479_ = l_Repr_addAppParen(v___x_5478_, v_prec_5465_);
return v___x_5479_;
}
v___jp_5480_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5482_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
v___x_5483_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5483_, 0, v___y_5481_);
lean_ctor_set(v___x_5483_, 1, v___x_5482_);
v___x_5484_ = 0;
v___x_5485_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5485_, 0, v___x_5483_);
lean_ctor_set_uint8(v___x_5485_, sizeof(void*)*1, v___x_5484_);
v___x_5486_ = l_Repr_addAppParen(v___x_5485_, v_prec_5465_);
return v___x_5486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5499_, lean_object* v_prec_5500_){
_start:
{
uint8_t v_x_173__boxed_5501_; lean_object* v_res_5502_; 
v_x_173__boxed_5501_ = lean_unbox(v_x_5499_);
v_res_5502_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_173__boxed_5501_, v_prec_5500_);
lean_dec(v_prec_5500_);
return v_res_5502_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = lean_unsigned_to_nat(8u);
v___x_5515_ = lean_nat_to_int(v___x_5514_);
return v___x_5515_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5525_ = lean_unsigned_to_nat(13u);
v___x_5526_ = lean_nat_to_int(v___x_5525_);
return v___x_5526_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_unsigned_to_nat(10u);
v___x_5537_ = lean_nat_to_int(v___x_5536_);
return v___x_5537_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___x_5541_ = lean_unsigned_to_nat(14u);
v___x_5542_ = lean_nat_to_int(v___x_5541_);
return v___x_5542_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5546_ = lean_unsigned_to_nat(19u);
v___x_5547_ = lean_nat_to_int(v___x_5546_);
return v___x_5547_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; 
v___x_5551_ = lean_unsigned_to_nat(20u);
v___x_5552_ = lean_nat_to_int(v___x_5551_);
return v___x_5552_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5559_; lean_object* v___x_5560_; 
v___x_5559_ = lean_unsigned_to_nat(9u);
v___x_5560_ = lean_nat_to_int(v___x_5559_);
return v___x_5560_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; 
v___x_5567_ = lean_unsigned_to_nat(12u);
v___x_5568_ = lean_nat_to_int(v___x_5567_);
return v___x_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5575_){
_start:
{
uint8_t v_zeta_5576_; uint8_t v_beta_5577_; uint8_t v_eta_5578_; uint8_t v_etaStruct_5579_; uint8_t v_iota_5580_; uint8_t v_proj_5581_; uint8_t v_decide_5582_; uint8_t v_autoUnfold_5583_; uint8_t v_failIfUnchanged_5584_; uint8_t v_unfoldPartialApp_5585_; uint8_t v_zetaDelta_5586_; uint8_t v_index_5587_; uint8_t v_zetaUnused_5588_; uint8_t v_zetaHave_5589_; uint8_t v_locals_5590_; uint8_t v_instances_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; uint8_t v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
v_zeta_5576_ = lean_ctor_get_uint8(v_x_5575_, 0);
v_beta_5577_ = lean_ctor_get_uint8(v_x_5575_, 1);
v_eta_5578_ = lean_ctor_get_uint8(v_x_5575_, 2);
v_etaStruct_5579_ = lean_ctor_get_uint8(v_x_5575_, 3);
v_iota_5580_ = lean_ctor_get_uint8(v_x_5575_, 4);
v_proj_5581_ = lean_ctor_get_uint8(v_x_5575_, 5);
v_decide_5582_ = lean_ctor_get_uint8(v_x_5575_, 6);
v_autoUnfold_5583_ = lean_ctor_get_uint8(v_x_5575_, 7);
v_failIfUnchanged_5584_ = lean_ctor_get_uint8(v_x_5575_, 8);
v_unfoldPartialApp_5585_ = lean_ctor_get_uint8(v_x_5575_, 9);
v_zetaDelta_5586_ = lean_ctor_get_uint8(v_x_5575_, 10);
v_index_5587_ = lean_ctor_get_uint8(v_x_5575_, 11);
v_zetaUnused_5588_ = lean_ctor_get_uint8(v_x_5575_, 12);
v_zetaHave_5589_ = lean_ctor_get_uint8(v_x_5575_, 13);
v_locals_5590_ = lean_ctor_get_uint8(v_x_5575_, 14);
v_instances_5591_ = lean_ctor_get_uint8(v_x_5575_, 15);
v___x_5592_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5593_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5594_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5595_ = lean_unsigned_to_nat(0u);
v___x_5596_ = l_Bool_repr___redArg(v_zeta_5576_);
v___x_5597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5597_, 0, v___x_5594_);
lean_ctor_set(v___x_5597_, 1, v___x_5596_);
v___x_5598_ = 0;
v___x_5599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5599_, 0, v___x_5597_);
lean_ctor_set_uint8(v___x_5599_, sizeof(void*)*1, v___x_5598_);
v___x_5600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5600_, 0, v___x_5593_);
lean_ctor_set(v___x_5600_, 1, v___x_5599_);
v___x_5601_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5602_, 0, v___x_5600_);
lean_ctor_set(v___x_5602_, 1, v___x_5601_);
v___x_5603_ = lean_box(1);
v___x_5604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5602_);
lean_ctor_set(v___x_5604_, 1, v___x_5603_);
v___x_5605_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5604_);
lean_ctor_set(v___x_5606_, 1, v___x_5605_);
v___x_5607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5606_);
lean_ctor_set(v___x_5607_, 1, v___x_5592_);
v___x_5608_ = l_Bool_repr___redArg(v_beta_5577_);
v___x_5609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5594_);
lean_ctor_set(v___x_5609_, 1, v___x_5608_);
v___x_5610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
lean_ctor_set_uint8(v___x_5610_, sizeof(void*)*1, v___x_5598_);
v___x_5611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5607_);
lean_ctor_set(v___x_5611_, 1, v___x_5610_);
v___x_5612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5611_);
lean_ctor_set(v___x_5612_, 1, v___x_5601_);
v___x_5613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5612_);
lean_ctor_set(v___x_5613_, 1, v___x_5603_);
v___x_5614_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5613_);
lean_ctor_set(v___x_5615_, 1, v___x_5614_);
v___x_5616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
lean_ctor_set(v___x_5616_, 1, v___x_5592_);
v___x_5617_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5618_ = l_Bool_repr___redArg(v_eta_5578_);
v___x_5619_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5617_);
lean_ctor_set(v___x_5619_, 1, v___x_5618_);
v___x_5620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5620_, 0, v___x_5619_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*1, v___x_5598_);
v___x_5621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5616_);
lean_ctor_set(v___x_5621_, 1, v___x_5620_);
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
lean_ctor_set(v___x_5622_, 1, v___x_5601_);
v___x_5623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set(v___x_5623_, 1, v___x_5603_);
v___x_5624_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5623_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v___x_5592_);
v___x_5627_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5628_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5579_, v___x_5595_);
v___x_5629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5627_);
lean_ctor_set(v___x_5629_, 1, v___x_5628_);
v___x_5630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5630_, 0, v___x_5629_);
lean_ctor_set_uint8(v___x_5630_, sizeof(void*)*1, v___x_5598_);
v___x_5631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5626_);
lean_ctor_set(v___x_5631_, 1, v___x_5630_);
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
lean_ctor_set(v___x_5632_, 1, v___x_5601_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v___x_5603_);
v___x_5634_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5633_);
lean_ctor_set(v___x_5635_, 1, v___x_5634_);
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5635_);
lean_ctor_set(v___x_5636_, 1, v___x_5592_);
v___x_5637_ = l_Bool_repr___redArg(v_iota_5580_);
v___x_5638_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5594_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
lean_ctor_set_uint8(v___x_5639_, sizeof(void*)*1, v___x_5598_);
v___x_5640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5636_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
lean_ctor_set(v___x_5641_, 1, v___x_5601_);
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
lean_ctor_set(v___x_5642_, 1, v___x_5603_);
v___x_5643_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5642_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v___x_5592_);
v___x_5646_ = l_Bool_repr___redArg(v_proj_5581_);
v___x_5647_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5594_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
lean_ctor_set_uint8(v___x_5648_, sizeof(void*)*1, v___x_5598_);
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5645_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set(v___x_5650_, 1, v___x_5601_);
v___x_5651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set(v___x_5651_, 1, v___x_5603_);
v___x_5652_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5651_);
lean_ctor_set(v___x_5653_, 1, v___x_5652_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v___x_5592_);
v___x_5655_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5656_ = l_Bool_repr___redArg(v_decide_5582_);
v___x_5657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5655_);
lean_ctor_set(v___x_5657_, 1, v___x_5656_);
v___x_5658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
lean_ctor_set_uint8(v___x_5658_, sizeof(void*)*1, v___x_5598_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5654_);
lean_ctor_set(v___x_5659_, 1, v___x_5658_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set(v___x_5660_, 1, v___x_5601_);
v___x_5661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set(v___x_5661_, 1, v___x_5603_);
v___x_5662_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5661_);
lean_ctor_set(v___x_5663_, 1, v___x_5662_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5592_);
v___x_5665_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5666_ = l_Bool_repr___redArg(v_autoUnfold_5583_);
v___x_5667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5665_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set_uint8(v___x_5668_, sizeof(void*)*1, v___x_5598_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5664_);
lean_ctor_set(v___x_5669_, 1, v___x_5668_);
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5669_);
lean_ctor_set(v___x_5670_, 1, v___x_5601_);
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set(v___x_5671_, 1, v___x_5603_);
v___x_5672_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5671_);
lean_ctor_set(v___x_5673_, 1, v___x_5672_);
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5673_);
lean_ctor_set(v___x_5674_, 1, v___x_5592_);
v___x_5675_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5676_ = l_Bool_repr___redArg(v_failIfUnchanged_5584_);
v___x_5677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5675_);
lean_ctor_set(v___x_5677_, 1, v___x_5676_);
v___x_5678_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set_uint8(v___x_5678_, sizeof(void*)*1, v___x_5598_);
v___x_5679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5674_);
lean_ctor_set(v___x_5679_, 1, v___x_5678_);
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
lean_ctor_set(v___x_5680_, 1, v___x_5601_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5680_);
lean_ctor_set(v___x_5681_, 1, v___x_5603_);
v___x_5682_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5681_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5683_);
lean_ctor_set(v___x_5684_, 1, v___x_5592_);
v___x_5685_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5686_ = l_Bool_repr___redArg(v_unfoldPartialApp_5585_);
v___x_5687_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5685_);
lean_ctor_set(v___x_5687_, 1, v___x_5686_);
v___x_5688_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set_uint8(v___x_5688_, sizeof(void*)*1, v___x_5598_);
v___x_5689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5684_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
lean_ctor_set(v___x_5690_, 1, v___x_5601_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5603_);
v___x_5692_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5691_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
lean_ctor_set(v___x_5694_, 1, v___x_5592_);
v___x_5695_ = l_Bool_repr___redArg(v_zetaDelta_5586_);
v___x_5696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5627_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
lean_ctor_set_uint8(v___x_5697_, sizeof(void*)*1, v___x_5598_);
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5694_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set(v___x_5699_, 1, v___x_5601_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set(v___x_5700_, 1, v___x_5603_);
v___x_5701_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
lean_ctor_set(v___x_5703_, 1, v___x_5592_);
v___x_5704_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5705_ = l_Bool_repr___redArg(v_index_5587_);
v___x_5706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5704_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
v___x_5707_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
lean_ctor_set_uint8(v___x_5707_, sizeof(void*)*1, v___x_5598_);
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5703_);
lean_ctor_set(v___x_5708_, 1, v___x_5707_);
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set(v___x_5709_, 1, v___x_5601_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set(v___x_5710_, 1, v___x_5603_);
v___x_5711_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5710_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set(v___x_5713_, 1, v___x_5592_);
v___x_5714_ = l_Bool_repr___redArg(v_zetaUnused_5588_);
v___x_5715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5665_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5716_, 0, v___x_5715_);
lean_ctor_set_uint8(v___x_5716_, sizeof(void*)*1, v___x_5598_);
v___x_5717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5713_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set(v___x_5718_, 1, v___x_5601_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v___x_5603_);
v___x_5720_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5719_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5721_);
lean_ctor_set(v___x_5722_, 1, v___x_5592_);
v___x_5723_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5724_ = l_Bool_repr___redArg(v_zetaHave_5589_);
v___x_5725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5723_);
lean_ctor_set(v___x_5725_, 1, v___x_5724_);
v___x_5726_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5726_, 0, v___x_5725_);
lean_ctor_set_uint8(v___x_5726_, sizeof(void*)*1, v___x_5598_);
v___x_5727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5722_);
lean_ctor_set(v___x_5727_, 1, v___x_5726_);
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
lean_ctor_set(v___x_5728_, 1, v___x_5601_);
v___x_5729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set(v___x_5729_, 1, v___x_5603_);
v___x_5730_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5729_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5731_);
lean_ctor_set(v___x_5732_, 1, v___x_5592_);
v___x_5733_ = l_Bool_repr___redArg(v_locals_5590_);
v___x_5734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5655_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
lean_ctor_set_uint8(v___x_5735_, sizeof(void*)*1, v___x_5598_);
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5732_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v___x_5601_);
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5737_);
lean_ctor_set(v___x_5738_, 1, v___x_5603_);
v___x_5739_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5738_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5740_);
lean_ctor_set(v___x_5741_, 1, v___x_5592_);
v___x_5742_ = l_Bool_repr___redArg(v_instances_5591_);
v___x_5743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5627_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set_uint8(v___x_5744_, sizeof(void*)*1, v___x_5598_);
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5741_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5747_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set(v___x_5748_, 1, v___x_5745_);
v___x_5749_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5748_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
v___x_5751_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5746_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
lean_ctor_set_uint8(v___x_5752_, sizeof(void*)*1, v___x_5598_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5753_){
_start:
{
lean_object* v_res_5754_; 
v_res_5754_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5753_);
lean_dec_ref(v_x_5753_);
return v_res_5754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5755_, lean_object* v_prec_5756_){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5755_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5758_, lean_object* v_prec_5759_){
_start:
{
lean_object* v_res_5760_; 
v_res_5760_ = l_Lean_Meta_instReprConfig_repr(v_x_5758_, v_prec_5759_);
lean_dec(v_prec_5759_);
lean_dec_ref(v_x_5758_);
return v_res_5760_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5768_, lean_object* v_x_5769_){
_start:
{
if (lean_obj_tag(v_x_5768_) == 0)
{
lean_object* v___x_5770_; 
v___x_5770_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5770_;
}
else
{
lean_object* v_val_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5782_; 
v_val_5771_ = lean_ctor_get(v_x_5768_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v_x_5768_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5773_ = v_x_5768_;
v_isShared_5774_ = v_isSharedCheck_5782_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_val_5771_);
lean_dec(v_x_5768_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5782_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5778_; 
v___x_5775_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5776_ = l_Nat_reprFast(v_val_5771_);
if (v_isShared_5774_ == 0)
{
lean_ctor_set_tag(v___x_5773_, 3);
lean_ctor_set(v___x_5773_, 0, v___x_5776_);
v___x_5778_ = v___x_5773_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; 
v___x_5779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5775_);
lean_ctor_set(v___x_5779_, 1, v___x_5778_);
v___x_5780_ = l_Repr_addAppParen(v___x_5779_, v_x_5769_);
return v___x_5780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5783_, lean_object* v_x_5784_){
_start:
{
lean_object* v_res_5785_; 
v_res_5785_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5783_, v_x_5784_);
lean_dec(v_x_5784_);
return v_res_5785_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5798_; lean_object* v___x_5799_; 
v___x_5798_ = lean_unsigned_to_nat(21u);
v___x_5799_ = lean_nat_to_int(v___x_5798_);
return v___x_5799_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5806_; lean_object* v___x_5807_; 
v___x_5806_ = lean_unsigned_to_nat(11u);
v___x_5807_ = lean_nat_to_int(v___x_5806_);
return v___x_5807_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5823_ = lean_unsigned_to_nat(23u);
v___x_5824_ = lean_nat_to_int(v___x_5823_);
return v___x_5824_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5828_ = lean_unsigned_to_nat(16u);
v___x_5829_ = lean_nat_to_int(v___x_5828_);
return v___x_5829_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5836_ = lean_unsigned_to_nat(15u);
v___x_5837_ = lean_nat_to_int(v___x_5836_);
return v___x_5837_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5844_ = lean_unsigned_to_nat(17u);
v___x_5845_ = lean_nat_to_int(v___x_5844_);
return v___x_5845_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = lean_unsigned_to_nat(18u);
v___x_5853_ = lean_nat_to_int(v___x_5852_);
return v___x_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5854_){
_start:
{
lean_object* v_maxSteps_5855_; lean_object* v_maxDischargeDepth_5856_; uint8_t v_contextual_5857_; uint8_t v_memoize_5858_; uint8_t v_singlePass_5859_; uint8_t v_zeta_5860_; uint8_t v_beta_5861_; uint8_t v_eta_5862_; uint8_t v_etaStruct_5863_; uint8_t v_iota_5864_; uint8_t v_proj_5865_; uint8_t v_decide_5866_; uint8_t v_arith_5867_; uint8_t v_autoUnfold_5868_; uint8_t v_dsimp_5869_; uint8_t v_failIfUnchanged_5870_; uint8_t v_ground_5871_; uint8_t v_unfoldPartialApp_5872_; uint8_t v_zetaDelta_5873_; uint8_t v_index_5874_; uint8_t v_implicitDefEqProofs_5875_; uint8_t v_zetaUnused_5876_; uint8_t v_catchRuntime_5877_; uint8_t v_zetaHave_5878_; uint8_t v_letToHave_5879_; uint8_t v_congrConsts_5880_; uint8_t v_bitVecOfNat_5881_; uint8_t v_warnExponents_5882_; uint8_t v_suggestions_5883_; lean_object* v_maxSuggestions_5884_; uint8_t v_locals_5885_; uint8_t v_instances_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; uint8_t v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v_maxSteps_5855_ = lean_ctor_get(v_x_5854_, 0);
lean_inc(v_maxSteps_5855_);
v_maxDischargeDepth_5856_ = lean_ctor_get(v_x_5854_, 1);
lean_inc(v_maxDischargeDepth_5856_);
v_contextual_5857_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3);
v_memoize_5858_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 1);
v_singlePass_5859_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 2);
v_zeta_5860_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 3);
v_beta_5861_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 4);
v_eta_5862_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 5);
v_etaStruct_5863_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 6);
v_iota_5864_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 7);
v_proj_5865_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 8);
v_decide_5866_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 9);
v_arith_5867_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 10);
v_autoUnfold_5868_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 11);
v_dsimp_5869_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5870_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 13);
v_ground_5871_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5872_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 15);
v_zetaDelta_5873_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 16);
v_index_5874_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5875_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 18);
v_zetaUnused_5876_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 19);
v_catchRuntime_5877_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 20);
v_zetaHave_5878_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 21);
v_letToHave_5879_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 22);
v_congrConsts_5880_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5881_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 24);
v_warnExponents_5882_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 25);
v_suggestions_5883_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 26);
v_maxSuggestions_5884_ = lean_ctor_get(v_x_5854_, 2);
lean_inc(v_maxSuggestions_5884_);
v_locals_5885_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 27);
v_instances_5886_ = lean_ctor_get_uint8(v_x_5854_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5854_);
v___x_5887_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5888_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5889_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5890_ = l_Nat_reprFast(v_maxSteps_5855_);
v___x_5891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5891_, 0, v___x_5890_);
v___x_5892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5889_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = 0;
v___x_5894_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5894_, 0, v___x_5892_);
lean_ctor_set_uint8(v___x_5894_, sizeof(void*)*1, v___x_5893_);
v___x_5895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5888_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5895_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
v___x_5898_ = lean_box(1);
v___x_5899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5897_);
lean_ctor_set(v___x_5899_, 1, v___x_5898_);
v___x_5900_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5899_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
v___x_5902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5901_);
lean_ctor_set(v___x_5902_, 1, v___x_5887_);
v___x_5903_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5904_ = l_Nat_reprFast(v_maxDischargeDepth_5856_);
v___x_5905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5904_);
v___x_5906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5903_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5907_, 0, v___x_5906_);
lean_ctor_set_uint8(v___x_5907_, sizeof(void*)*1, v___x_5893_);
v___x_5908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5902_);
lean_ctor_set(v___x_5908_, 1, v___x_5907_);
v___x_5909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5908_);
lean_ctor_set(v___x_5909_, 1, v___x_5896_);
v___x_5910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
lean_ctor_set(v___x_5910_, 1, v___x_5898_);
v___x_5911_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5912_);
lean_ctor_set(v___x_5913_, 1, v___x_5887_);
v___x_5914_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5915_ = lean_unsigned_to_nat(0u);
v___x_5916_ = l_Bool_repr___redArg(v_contextual_5857_);
v___x_5917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5914_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
v___x_5918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
lean_ctor_set_uint8(v___x_5918_, sizeof(void*)*1, v___x_5893_);
v___x_5919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5913_);
lean_ctor_set(v___x_5919_, 1, v___x_5918_);
v___x_5920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5919_);
lean_ctor_set(v___x_5920_, 1, v___x_5896_);
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5920_);
lean_ctor_set(v___x_5921_, 1, v___x_5898_);
v___x_5922_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5921_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5923_);
lean_ctor_set(v___x_5924_, 1, v___x_5887_);
v___x_5925_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5926_ = l_Bool_repr___redArg(v_memoize_5858_);
v___x_5927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5925_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
v___x_5928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*1, v___x_5893_);
v___x_5929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5924_);
lean_ctor_set(v___x_5929_, 1, v___x_5928_);
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
lean_ctor_set(v___x_5930_, 1, v___x_5896_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5898_);
v___x_5932_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5931_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5887_);
v___x_5935_ = l_Bool_repr___redArg(v_singlePass_5859_);
v___x_5936_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5914_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5937_, 0, v___x_5936_);
lean_ctor_set_uint8(v___x_5937_, sizeof(void*)*1, v___x_5893_);
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5934_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set(v___x_5939_, 1, v___x_5896_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5939_);
lean_ctor_set(v___x_5940_, 1, v___x_5898_);
v___x_5941_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5942_);
lean_ctor_set(v___x_5943_, 1, v___x_5887_);
v___x_5944_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5945_ = l_Bool_repr___redArg(v_zeta_5860_);
v___x_5946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set_uint8(v___x_5947_, sizeof(void*)*1, v___x_5893_);
v___x_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5943_);
lean_ctor_set(v___x_5948_, 1, v___x_5947_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set(v___x_5949_, 1, v___x_5896_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set(v___x_5950_, 1, v___x_5898_);
v___x_5951_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5950_);
lean_ctor_set(v___x_5952_, 1, v___x_5951_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5952_);
lean_ctor_set(v___x_5953_, 1, v___x_5887_);
v___x_5954_ = l_Bool_repr___redArg(v_beta_5861_);
v___x_5955_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5944_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5956_, 0, v___x_5955_);
lean_ctor_set_uint8(v___x_5956_, sizeof(void*)*1, v___x_5893_);
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5953_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5896_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
lean_ctor_set(v___x_5959_, 1, v___x_5898_);
v___x_5960_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5959_);
lean_ctor_set(v___x_5961_, 1, v___x_5960_);
v___x_5962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_ctor_set(v___x_5962_, 1, v___x_5887_);
v___x_5963_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5964_ = l_Bool_repr___redArg(v_eta_5862_);
v___x_5965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5963_);
lean_ctor_set(v___x_5965_, 1, v___x_5964_);
v___x_5966_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set_uint8(v___x_5966_, sizeof(void*)*1, v___x_5893_);
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5962_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5967_);
lean_ctor_set(v___x_5968_, 1, v___x_5896_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5898_);
v___x_5970_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5969_);
lean_ctor_set(v___x_5971_, 1, v___x_5970_);
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
lean_ctor_set(v___x_5972_, 1, v___x_5887_);
v___x_5973_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5974_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5863_, v___x_5915_);
v___x_5975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5973_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set_uint8(v___x_5976_, sizeof(void*)*1, v___x_5893_);
v___x_5977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5972_);
lean_ctor_set(v___x_5977_, 1, v___x_5976_);
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5977_);
lean_ctor_set(v___x_5978_, 1, v___x_5896_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5898_);
v___x_5980_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5979_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5981_);
lean_ctor_set(v___x_5982_, 1, v___x_5887_);
v___x_5983_ = l_Bool_repr___redArg(v_iota_5864_);
v___x_5984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5944_);
lean_ctor_set(v___x_5984_, 1, v___x_5983_);
v___x_5985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
lean_ctor_set_uint8(v___x_5985_, sizeof(void*)*1, v___x_5893_);
v___x_5986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5982_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5896_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set(v___x_5988_, 1, v___x_5898_);
v___x_5989_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5988_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
lean_ctor_set(v___x_5991_, 1, v___x_5887_);
v___x_5992_ = l_Bool_repr___redArg(v_proj_5865_);
v___x_5993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5944_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set_uint8(v___x_5994_, sizeof(void*)*1, v___x_5893_);
v___x_5995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5991_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v___x_5896_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set(v___x_5997_, 1, v___x_5898_);
v___x_5998_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5997_);
lean_ctor_set(v___x_5999_, 1, v___x_5998_);
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set(v___x_6000_, 1, v___x_5887_);
v___x_6001_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6002_ = l_Bool_repr___redArg(v_decide_5866_);
v___x_6003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6001_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
v___x_6004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set_uint8(v___x_6004_, sizeof(void*)*1, v___x_5893_);
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6000_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___x_5896_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5898_);
v___x_6008_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6007_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set(v___x_6010_, 1, v___x_5887_);
v___x_6011_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6012_ = l_Bool_repr___redArg(v_arith_5867_);
v___x_6013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6011_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
v___x_6014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set_uint8(v___x_6014_, sizeof(void*)*1, v___x_5893_);
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6010_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5896_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5898_);
v___x_6018_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6017_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_5887_);
v___x_6021_ = l_Bool_repr___redArg(v_autoUnfold_5868_);
v___x_6022_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_5914_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set_uint8(v___x_6023_, sizeof(void*)*1, v___x_5893_);
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6020_);
lean_ctor_set(v___x_6024_, 1, v___x_6023_);
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set(v___x_6025_, 1, v___x_5896_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_5898_);
v___x_6027_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6026_);
lean_ctor_set(v___x_6028_, 1, v___x_6027_);
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set(v___x_6029_, 1, v___x_5887_);
v___x_6030_ = l_Bool_repr___redArg(v_dsimp_5869_);
v___x_6031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6011_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set_uint8(v___x_6032_, sizeof(void*)*1, v___x_5893_);
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6029_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set(v___x_6034_, 1, v___x_5896_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set(v___x_6035_, 1, v___x_5898_);
v___x_6036_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6035_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_5887_);
v___x_6039_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6040_ = l_Bool_repr___redArg(v_failIfUnchanged_5870_);
v___x_6041_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6039_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set_uint8(v___x_6042_, sizeof(void*)*1, v___x_5893_);
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6038_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_5896_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set(v___x_6045_, 1, v___x_5898_);
v___x_6046_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6045_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set(v___x_6048_, 1, v___x_5887_);
v___x_6049_ = l_Bool_repr___redArg(v_ground_5871_);
v___x_6050_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6001_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set_uint8(v___x_6051_, sizeof(void*)*1, v___x_5893_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6048_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set(v___x_6053_, 1, v___x_5896_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5898_);
v___x_6055_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6054_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set(v___x_6057_, 1, v___x_5887_);
v___x_6058_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6059_ = l_Bool_repr___redArg(v_unfoldPartialApp_5872_);
v___x_6060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6058_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set_uint8(v___x_6061_, sizeof(void*)*1, v___x_5893_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6057_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5896_);
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set(v___x_6064_, 1, v___x_5898_);
v___x_6065_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6064_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v___x_5887_);
v___x_6068_ = l_Bool_repr___redArg(v_zetaDelta_5873_);
v___x_6069_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_5973_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set_uint8(v___x_6070_, sizeof(void*)*1, v___x_5893_);
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6067_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_5896_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_5898_);
v___x_6074_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6073_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set(v___x_6076_, 1, v___x_5887_);
v___x_6077_ = l_Bool_repr___redArg(v_index_5874_);
v___x_6078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6011_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set_uint8(v___x_6079_, sizeof(void*)*1, v___x_5893_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6076_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6080_);
lean_ctor_set(v___x_6081_, 1, v___x_5896_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5898_);
v___x_6083_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6082_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5887_);
v___x_6086_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6087_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5875_);
v___x_6088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6086_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set_uint8(v___x_6089_, sizeof(void*)*1, v___x_5893_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6085_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_5896_);
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
lean_ctor_set(v___x_6092_, 1, v___x_5898_);
v___x_6093_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6092_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set(v___x_6095_, 1, v___x_5887_);
v___x_6096_ = l_Bool_repr___redArg(v_zetaUnused_5876_);
v___x_6097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_5914_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set_uint8(v___x_6098_, sizeof(void*)*1, v___x_5893_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6095_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_5896_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5898_);
v___x_6102_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_5887_);
v___x_6105_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6106_ = l_Bool_repr___redArg(v_catchRuntime_5877_);
v___x_6107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6105_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set_uint8(v___x_6108_, sizeof(void*)*1, v___x_5893_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6104_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_5896_);
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set(v___x_6111_, 1, v___x_5898_);
v___x_6112_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6111_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set(v___x_6114_, 1, v___x_5887_);
v___x_6115_ = l_Bool_repr___redArg(v_zetaHave_5878_);
v___x_6116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_5889_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set_uint8(v___x_6117_, sizeof(void*)*1, v___x_5893_);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6114_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_5896_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_5898_);
v___x_6121_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6120_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set(v___x_6123_, 1, v___x_5887_);
v___x_6124_ = l_Bool_repr___redArg(v_letToHave_5879_);
v___x_6125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_5973_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set_uint8(v___x_6126_, sizeof(void*)*1, v___x_5893_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6123_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
lean_ctor_set(v___x_6128_, 1, v___x_5896_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_5898_);
v___x_6130_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6129_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5887_);
v___x_6133_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6134_ = l_Bool_repr___redArg(v_congrConsts_5880_);
v___x_6135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6133_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
v___x_6136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set_uint8(v___x_6136_, sizeof(void*)*1, v___x_5893_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6132_);
lean_ctor_set(v___x_6137_, 1, v___x_6136_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_5896_);
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set(v___x_6139_, 1, v___x_5898_);
v___x_6140_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6139_);
lean_ctor_set(v___x_6141_, 1, v___x_6140_);
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6141_);
lean_ctor_set(v___x_6142_, 1, v___x_5887_);
v___x_6143_ = l_Bool_repr___redArg(v_bitVecOfNat_5881_);
v___x_6144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6133_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*1, v___x_5893_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6142_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set(v___x_6147_, 1, v___x_5896_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_5898_);
v___x_6149_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_5887_);
v___x_6152_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6153_ = l_Bool_repr___redArg(v_warnExponents_5882_);
v___x_6154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6152_);
lean_ctor_set(v___x_6154_, 1, v___x_6153_);
v___x_6155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set_uint8(v___x_6155_, sizeof(void*)*1, v___x_5893_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6151_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set(v___x_6157_, 1, v___x_5896_);
v___x_6158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
lean_ctor_set(v___x_6158_, 1, v___x_5898_);
v___x_6159_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6158_);
lean_ctor_set(v___x_6160_, 1, v___x_6159_);
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
lean_ctor_set(v___x_6161_, 1, v___x_5887_);
v___x_6162_ = l_Bool_repr___redArg(v_suggestions_5883_);
v___x_6163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6133_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
lean_ctor_set_uint8(v___x_6164_, sizeof(void*)*1, v___x_5893_);
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6161_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set(v___x_6166_, 1, v___x_5896_);
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6166_);
lean_ctor_set(v___x_6167_, 1, v___x_5898_);
v___x_6168_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6167_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
lean_ctor_set(v___x_6170_, 1, v___x_5887_);
v___x_6171_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6172_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5884_, v___x_5915_);
v___x_6173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6171_);
lean_ctor_set(v___x_6173_, 1, v___x_6172_);
v___x_6174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6174_, 0, v___x_6173_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*1, v___x_5893_);
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6170_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set(v___x_6176_, 1, v___x_5896_);
v___x_6177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set(v___x_6177_, 1, v___x_5898_);
v___x_6178_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6177_);
lean_ctor_set(v___x_6179_, 1, v___x_6178_);
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6179_);
lean_ctor_set(v___x_6180_, 1, v___x_5887_);
v___x_6181_ = l_Bool_repr___redArg(v_locals_5885_);
v___x_6182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6001_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
v___x_6183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6183_, 0, v___x_6182_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*1, v___x_5893_);
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6180_);
lean_ctor_set(v___x_6184_, 1, v___x_6183_);
v___x_6185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___x_5896_);
v___x_6186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6185_);
lean_ctor_set(v___x_6186_, 1, v___x_5898_);
v___x_6187_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
lean_ctor_set(v___x_6189_, 1, v___x_5887_);
v___x_6190_ = l_Bool_repr___redArg(v_instances_5886_);
v___x_6191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_5973_);
lean_ctor_set(v___x_6191_, 1, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set_uint8(v___x_6192_, sizeof(void*)*1, v___x_5893_);
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6189_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6195_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
lean_ctor_set(v___x_6196_, 1, v___x_6193_);
v___x_6197_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6196_);
lean_ctor_set(v___x_6198_, 1, v___x_6197_);
v___x_6199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6194_);
lean_ctor_set(v___x_6199_, 1, v___x_6198_);
v___x_6200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6200_, 0, v___x_6199_);
lean_ctor_set_uint8(v___x_6200_, sizeof(void*)*1, v___x_5893_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6201_, lean_object* v_prec_6202_){
_start:
{
lean_object* v___x_6203_; 
v___x_6203_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6201_);
return v___x_6203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6204_, lean_object* v_prec_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6204_, v_prec_6205_);
lean_dec(v_prec_6205_);
return v_res_6206_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6209_, lean_object* v_x_6210_){
_start:
{
if (lean_obj_tag(v_x_6210_) == 0)
{
uint8_t v___x_6211_; 
v___x_6211_ = 0;
return v___x_6211_;
}
else
{
lean_object* v_head_6212_; lean_object* v_tail_6213_; uint8_t v___x_6214_; 
v_head_6212_ = lean_ctor_get(v_x_6210_, 0);
v_tail_6213_ = lean_ctor_get(v_x_6210_, 1);
v___x_6214_ = lean_nat_dec_eq(v_a_6209_, v_head_6212_);
if (v___x_6214_ == 0)
{
v_x_6210_ = v_tail_6213_;
goto _start;
}
else
{
return v___x_6214_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6216_, lean_object* v_x_6217_){
_start:
{
uint8_t v_res_6218_; lean_object* v_r_6219_; 
v_res_6218_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6216_, v_x_6217_);
lean_dec(v_x_6217_);
lean_dec(v_a_6216_);
v_r_6219_ = lean_box(v_res_6218_);
return v_r_6219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6220_, lean_object* v_x_6221_){
_start:
{
switch(lean_obj_tag(v_x_6220_))
{
case 0:
{
uint8_t v___x_6222_; 
v___x_6222_ = 1;
return v___x_6222_;
}
case 1:
{
lean_object* v_idxs_6223_; uint8_t v___x_6224_; 
v_idxs_6223_ = lean_ctor_get(v_x_6220_, 0);
v___x_6224_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6221_, v_idxs_6223_);
return v___x_6224_;
}
default: 
{
lean_object* v_idxs_6225_; uint8_t v___x_6226_; 
v_idxs_6225_ = lean_ctor_get(v_x_6220_, 0);
v___x_6226_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6221_, v_idxs_6225_);
if (v___x_6226_ == 0)
{
uint8_t v___x_6227_; 
v___x_6227_ = 1;
return v___x_6227_;
}
else
{
uint8_t v___x_6228_; 
v___x_6228_ = 0;
return v___x_6228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6229_, lean_object* v_x_6230_){
_start:
{
uint8_t v_res_6231_; lean_object* v_r_6232_; 
v_res_6231_ = l_Lean_Meta_Occurrences_contains(v_x_6229_, v_x_6230_);
lean_dec(v_x_6230_);
lean_dec(v_x_6229_);
v_r_6232_ = lean_box(v_res_6231_);
return v_r_6232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6233_){
_start:
{
if (lean_obj_tag(v_x_6233_) == 0)
{
uint8_t v___x_6234_; 
v___x_6234_ = 1;
return v___x_6234_;
}
else
{
uint8_t v___x_6235_; 
v___x_6235_ = 0;
return v___x_6235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6236_){
_start:
{
uint8_t v_res_6237_; lean_object* v_r_6238_; 
v_res_6237_ = l_Lean_Meta_Occurrences_isAll(v_x_6236_);
lean_dec(v_x_6236_);
v_r_6238_ = lean_box(v_res_6237_);
return v_r_6238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6239_){
_start:
{
switch(v_x_6239_)
{
case 0:
{
lean_object* v___x_6240_; 
v___x_6240_ = lean_unsigned_to_nat(0u);
return v___x_6240_;
}
case 1:
{
lean_object* v___x_6241_; 
v___x_6241_ = lean_unsigned_to_nat(1u);
return v___x_6241_;
}
default: 
{
lean_object* v___x_6242_; 
v___x_6242_ = lean_unsigned_to_nat(2u);
return v___x_6242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6243_){
_start:
{
uint8_t v_x_boxed_6244_; lean_object* v_res_6245_; 
v_x_boxed_6244_ = lean_unbox(v_x_6243_);
v_res_6245_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6244_);
return v_res_6245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t v_x_6246_){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_6246_);
return v___x_6247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object* v_x_6248_){
_start:
{
uint8_t v_x_4__boxed_6249_; lean_object* v_res_6250_; 
v_x_4__boxed_6249_ = lean_unbox(v_x_6248_);
v_res_6250_ = l_Lean_Meta_ApplyNewGoals_toCtorIdx(v_x_4__boxed_6249_);
return v_res_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6251_){
_start:
{
lean_inc(v_k_6251_);
return v_k_6251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6252_){
_start:
{
lean_object* v_res_6253_; 
v_res_6253_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6252_);
lean_dec(v_k_6252_);
return v_res_6253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6254_, lean_object* v_ctorIdx_6255_, uint8_t v_t_6256_, lean_object* v_h_6257_, lean_object* v_k_6258_){
_start:
{
lean_inc(v_k_6258_);
return v_k_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6259_, lean_object* v_ctorIdx_6260_, lean_object* v_t_6261_, lean_object* v_h_6262_, lean_object* v_k_6263_){
_start:
{
uint8_t v_t_boxed_6264_; lean_object* v_res_6265_; 
v_t_boxed_6264_ = lean_unbox(v_t_6261_);
v_res_6265_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6259_, v_ctorIdx_6260_, v_t_boxed_6264_, v_h_6262_, v_k_6263_);
lean_dec(v_k_6263_);
lean_dec(v_ctorIdx_6260_);
return v_res_6265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6266_){
_start:
{
lean_inc(v_nonDependentFirst_6266_);
return v_nonDependentFirst_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6267_){
_start:
{
lean_object* v_res_6268_; 
v_res_6268_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6267_);
lean_dec(v_nonDependentFirst_6267_);
return v_res_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6269_, uint8_t v_t_6270_, lean_object* v_h_6271_, lean_object* v_nonDependentFirst_6272_){
_start:
{
lean_inc(v_nonDependentFirst_6272_);
return v_nonDependentFirst_6272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6273_, lean_object* v_t_6274_, lean_object* v_h_6275_, lean_object* v_nonDependentFirst_6276_){
_start:
{
uint8_t v_t_boxed_6277_; lean_object* v_res_6278_; 
v_t_boxed_6277_ = lean_unbox(v_t_6274_);
v_res_6278_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6273_, v_t_boxed_6277_, v_h_6275_, v_nonDependentFirst_6276_);
lean_dec(v_nonDependentFirst_6276_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6279_){
_start:
{
lean_inc(v_nonDependentOnly_6279_);
return v_nonDependentOnly_6279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6280_){
_start:
{
lean_object* v_res_6281_; 
v_res_6281_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6280_);
lean_dec(v_nonDependentOnly_6280_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6282_, uint8_t v_t_6283_, lean_object* v_h_6284_, lean_object* v_nonDependentOnly_6285_){
_start:
{
lean_inc(v_nonDependentOnly_6285_);
return v_nonDependentOnly_6285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6286_, lean_object* v_t_6287_, lean_object* v_h_6288_, lean_object* v_nonDependentOnly_6289_){
_start:
{
uint8_t v_t_boxed_6290_; lean_object* v_res_6291_; 
v_t_boxed_6290_ = lean_unbox(v_t_6287_);
v_res_6291_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6286_, v_t_boxed_6290_, v_h_6288_, v_nonDependentOnly_6289_);
lean_dec(v_nonDependentOnly_6289_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6292_){
_start:
{
lean_inc(v_all_6292_);
return v_all_6292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6293_){
_start:
{
lean_object* v_res_6294_; 
v_res_6294_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6293_);
lean_dec(v_all_6293_);
return v_res_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6295_, uint8_t v_t_6296_, lean_object* v_h_6297_, lean_object* v_all_6298_){
_start:
{
lean_inc(v_all_6298_);
return v_all_6298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6299_, lean_object* v_t_6300_, lean_object* v_h_6301_, lean_object* v_all_6302_){
_start:
{
uint8_t v_t_boxed_6303_; lean_object* v_res_6304_; 
v_t_boxed_6303_ = lean_unbox(v_t_6300_);
v_res_6304_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6299_, v_t_boxed_6303_, v_h_6301_, v_all_6302_);
lean_dec(v_all_6302_);
return v_res_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6318_){
_start:
{
lean_object* v___x_6319_; uint8_t v___x_6320_; 
v___x_6319_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6318_);
v___x_6320_ = l_Lean_Syntax_isOfKind(v_c_6318_, v___x_6319_);
if (v___x_6320_ == 0)
{
lean_object* v___x_6321_; uint8_t v___x_6322_; 
v___x_6321_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6318_);
v___x_6322_ = l_Lean_Syntax_isOfKind(v_c_6318_, v___x_6321_);
if (v___x_6322_ == 0)
{
lean_object* v___x_6323_; uint8_t v___x_6324_; 
v___x_6323_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6318_);
v___x_6324_ = l_Lean_Syntax_isOfKind(v_c_6318_, v___x_6323_);
if (v___x_6324_ == 0)
{
lean_object* v___x_6325_; 
lean_dec(v_c_6318_);
v___x_6325_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6325_;
}
else
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6326_ = lean_unsigned_to_nat(1u);
v___x_6327_ = lean_mk_empty_array_with_capacity(v___x_6326_);
v___x_6328_ = lean_array_push(v___x_6327_, v_c_6318_);
return v___x_6328_;
}
}
else
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_unsigned_to_nat(0u);
v___x_6330_ = l_Lean_Syntax_getArg(v_c_6318_, v___x_6329_);
lean_dec(v_c_6318_);
v___x_6331_ = l_Lean_Syntax_getArgs(v___x_6330_);
lean_dec(v___x_6330_);
return v___x_6331_;
}
}
else
{
lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; uint8_t v___x_6336_; 
v___x_6332_ = l_Lean_Syntax_getArgs(v_c_6318_);
lean_dec(v_c_6318_);
v___x_6333_ = lean_unsigned_to_nat(0u);
v___x_6334_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6335_ = lean_array_get_size(v___x_6332_);
v___x_6336_ = lean_nat_dec_lt(v___x_6333_, v___x_6335_);
if (v___x_6336_ == 0)
{
lean_dec_ref(v___x_6332_);
return v___x_6334_;
}
else
{
uint8_t v___x_6337_; 
v___x_6337_ = lean_nat_dec_le(v___x_6335_, v___x_6335_);
if (v___x_6337_ == 0)
{
if (v___x_6336_ == 0)
{
lean_dec_ref(v___x_6332_);
return v___x_6334_;
}
else
{
size_t v___x_6338_; size_t v___x_6339_; lean_object* v___x_6340_; 
v___x_6338_ = ((size_t)0ULL);
v___x_6339_ = lean_usize_of_nat(v___x_6335_);
v___x_6340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6332_, v___x_6338_, v___x_6339_, v___x_6334_);
lean_dec_ref(v___x_6332_);
return v___x_6340_;
}
}
else
{
size_t v___x_6341_; size_t v___x_6342_; lean_object* v___x_6343_; 
v___x_6341_ = ((size_t)0ULL);
v___x_6342_ = lean_usize_of_nat(v___x_6335_);
v___x_6343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6332_, v___x_6341_, v___x_6342_, v___x_6334_);
lean_dec_ref(v___x_6332_);
return v___x_6343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6344_, size_t v_i_6345_, size_t v_stop_6346_, lean_object* v_b_6347_){
_start:
{
uint8_t v___x_6348_; 
v___x_6348_ = lean_usize_dec_eq(v_i_6345_, v_stop_6346_);
if (v___x_6348_ == 0)
{
lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; size_t v___x_6352_; size_t v___x_6353_; 
v___x_6349_ = lean_array_uget_borrowed(v_as_6344_, v_i_6345_);
lean_inc(v___x_6349_);
v___x_6350_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6349_);
v___x_6351_ = l_Array_append___redArg(v_b_6347_, v___x_6350_);
lean_dec_ref(v___x_6350_);
v___x_6352_ = ((size_t)1ULL);
v___x_6353_ = lean_usize_add(v_i_6345_, v___x_6352_);
v_i_6345_ = v___x_6353_;
v_b_6347_ = v___x_6351_;
goto _start;
}
else
{
return v_b_6347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6355_, lean_object* v_i_6356_, lean_object* v_stop_6357_, lean_object* v_b_6358_){
_start:
{
size_t v_i_boxed_6359_; size_t v_stop_boxed_6360_; lean_object* v_res_6361_; 
v_i_boxed_6359_ = lean_unbox_usize(v_i_6356_);
lean_dec(v_i_6356_);
v_stop_boxed_6360_ = lean_unbox_usize(v_stop_6357_);
lean_dec(v_stop_6357_);
v_res_6361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6355_, v_i_boxed_6359_, v_stop_boxed_6360_, v_b_6358_);
lean_dec_ref(v_as_6355_);
return v_res_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6362_){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6363_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6364_ = lean_box(2);
v___x_6365_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6364_);
lean_ctor_set(v___x_6366_, 1, v___x_6365_);
lean_ctor_set(v___x_6366_, 2, v_items_6362_);
v___x_6367_ = l_Lean_Syntax_node1(v___x_6364_, v___x_6363_, v___x_6366_);
return v___x_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6368_, lean_object* v_cfg_x27_6369_){
_start:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6370_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6368_);
v___x_6371_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6369_);
v___x_6372_ = l_Array_append___redArg(v___x_6370_, v___x_6371_);
lean_dec_ref(v___x_6371_);
v___x_6373_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6372_);
return v___x_6373_;
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
