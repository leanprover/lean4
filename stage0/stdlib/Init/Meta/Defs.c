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
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_231_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 97;
v___x_238_ = lean_uint8_dec_le(v___x_237_, v_c_231_);
if (v___x_238_ == 0)
{
goto v___jp_232_;
}
else
{
uint8_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 122;
v___x_240_ = lean_uint8_dec_le(v_c_231_, v___x_239_);
if (v___x_240_ == 0)
{
goto v___jp_232_;
}
else
{
return v___x_240_;
}
}
v___jp_232_:
{
uint8_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 65;
v___x_234_ = lean_uint8_dec_le(v___x_233_, v_c_231_);
if (v___x_234_ == 0)
{
return v___x_234_;
}
else
{
uint8_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 90;
v___x_236_ = lean_uint8_dec_le(v_c_231_, v___x_235_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_241_){
_start:
{
uint8_t v_c_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_c_boxed_242_ = lean_unbox(v_c_241_);
v_res_243_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_245_){
_start:
{
uint8_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 97;
v___x_255_ = lean_uint8_dec_le(v___x_254_, v_c_245_);
if (v___x_255_ == 0)
{
goto v___jp_249_;
}
else
{
uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 122;
v___x_257_ = lean_uint8_dec_le(v_c_245_, v___x_256_);
if (v___x_257_ == 0)
{
goto v___jp_249_;
}
else
{
return v___x_257_;
}
}
v___jp_246_:
{
uint8_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 95;
v___x_248_ = lean_uint8_dec_eq(v_c_245_, v___x_247_);
return v___x_248_;
}
v___jp_249_:
{
uint8_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 65;
v___x_251_ = lean_uint8_dec_le(v___x_250_, v_c_245_);
if (v___x_251_ == 0)
{
goto v___jp_246_;
}
else
{
uint8_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 90;
v___x_253_ = lean_uint8_dec_le(v_c_245_, v___x_252_);
if (v___x_253_ == 0)
{
goto v___jp_246_;
}
else
{
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_258_){
_start:
{
uint8_t v_c_boxed_259_; uint8_t v_res_260_; lean_object* v_r_261_; 
v_c_boxed_259_ = lean_unbox(v_c_258_);
v_res_260_ = l_Lean_isIdFirstAscii(v_c_boxed_259_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_262_){
_start:
{
uint8_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 97;
v___x_274_ = lean_uint8_dec_le(v___x_273_, v_c_262_);
if (v___x_274_ == 0)
{
goto v___jp_268_;
}
else
{
uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_275_ = 122;
v___x_276_ = lean_uint8_dec_le(v_c_262_, v___x_275_);
if (v___x_276_ == 0)
{
goto v___jp_268_;
}
else
{
return v___x_276_;
}
}
v___jp_263_:
{
uint8_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 48;
v___x_265_ = lean_uint8_dec_le(v___x_264_, v_c_262_);
if (v___x_265_ == 0)
{
return v___x_265_;
}
else
{
uint8_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 57;
v___x_267_ = lean_uint8_dec_le(v_c_262_, v___x_266_);
return v___x_267_;
}
}
v___jp_268_:
{
uint8_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 65;
v___x_270_ = lean_uint8_dec_le(v___x_269_, v_c_262_);
if (v___x_270_ == 0)
{
goto v___jp_263_;
}
else
{
uint8_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 90;
v___x_272_ = lean_uint8_dec_le(v_c_262_, v___x_271_);
if (v___x_272_ == 0)
{
goto v___jp_263_;
}
else
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_277_){
_start:
{
uint8_t v_c_boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v_c_boxed_278_ = lean_unbox(v_c_277_);
v_res_279_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_281_){
_start:
{
uint8_t v___y_299_; uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 65;
v___x_305_ = lean_uint32_dec_le(v___x_304_, v_c_281_);
if (v___x_305_ == 0)
{
v___y_299_ = v___x_305_;
goto v___jp_298_;
}
else
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 90;
v___x_307_ = lean_uint32_dec_le(v_c_281_, v___x_306_);
v___y_299_ = v___x_307_;
goto v___jp_298_;
}
v___jp_282_:
{
uint32_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 95;
v___x_284_ = lean_uint32_dec_eq(v_c_281_, v___x_283_);
if (v___x_284_ == 0)
{
uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 39;
v___x_286_ = lean_uint32_dec_eq(v_c_281_, v___x_285_);
if (v___x_286_ == 0)
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 33;
v___x_288_ = lean_uint32_dec_eq(v_c_281_, v___x_287_);
if (v___x_288_ == 0)
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 63;
v___x_290_ = lean_uint32_dec_eq(v_c_281_, v___x_289_);
if (v___x_290_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = l_Lean_isLetterLike(v_c_281_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_isSubScriptAlnum(v_c_281_);
return v___x_292_;
}
else
{
return v___x_291_;
}
}
else
{
return v___x_290_;
}
}
else
{
return v___x_288_;
}
}
else
{
return v___x_286_;
}
}
else
{
return v___x_284_;
}
}
v___jp_293_:
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 48;
v___x_295_ = lean_uint32_dec_le(v___x_294_, v_c_281_);
if (v___x_295_ == 0)
{
goto v___jp_282_;
}
else
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 57;
v___x_297_ = lean_uint32_dec_le(v_c_281_, v___x_296_);
if (v___x_297_ == 0)
{
goto v___jp_282_;
}
else
{
return v___x_297_;
}
}
}
v___jp_298_:
{
if (v___y_299_ == 0)
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 97;
v___x_301_ = lean_uint32_dec_le(v___x_300_, v_c_281_);
if (v___x_301_ == 0)
{
goto v___jp_293_;
}
else
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 122;
v___x_303_ = lean_uint32_dec_le(v_c_281_, v___x_302_);
if (v___x_303_ == 0)
{
goto v___jp_293_;
}
else
{
return v___x_303_;
}
}
}
else
{
return v___y_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_308_){
_start:
{
uint32_t v_c_boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v_c_boxed_309_ = lean_unbox_uint32(v_c_308_);
lean_dec(v_c_308_);
v_res_310_ = l_Lean_isIdRest(v_c_boxed_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_312_){
_start:
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 97;
v___x_333_ = lean_uint8_dec_le(v___x_332_, v_c_312_);
if (v___x_333_ == 0)
{
goto v___jp_327_;
}
else
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 122;
v___x_335_ = lean_uint8_dec_le(v_c_312_, v___x_334_);
if (v___x_335_ == 0)
{
goto v___jp_327_;
}
else
{
return v___x_335_;
}
}
v___jp_313_:
{
uint8_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 95;
v___x_315_ = lean_uint8_dec_eq(v_c_312_, v___x_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 39;
v___x_317_ = lean_uint8_dec_eq(v_c_312_, v___x_316_);
if (v___x_317_ == 0)
{
uint8_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 33;
v___x_319_ = lean_uint8_dec_eq(v_c_312_, v___x_318_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 63;
v___x_321_ = lean_uint8_dec_eq(v_c_312_, v___x_320_);
return v___x_321_;
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
v___jp_322_:
{
uint8_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 48;
v___x_324_ = lean_uint8_dec_le(v___x_323_, v_c_312_);
if (v___x_324_ == 0)
{
goto v___jp_313_;
}
else
{
uint8_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 57;
v___x_326_ = lean_uint8_dec_le(v_c_312_, v___x_325_);
if (v___x_326_ == 0)
{
goto v___jp_313_;
}
else
{
return v___x_326_;
}
}
}
v___jp_327_:
{
uint8_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 65;
v___x_329_ = lean_uint8_dec_le(v___x_328_, v_c_312_);
if (v___x_329_ == 0)
{
goto v___jp_322_;
}
else
{
uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 90;
v___x_331_ = lean_uint8_dec_le(v_c_312_, v___x_330_);
if (v___x_331_ == 0)
{
goto v___jp_322_;
}
else
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_336_){
_start:
{
uint8_t v_c_boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_c_boxed_337_ = lean_unbox(v_c_336_);
v_res_338_ = l_Lean_isIdRestAscii(v_c_boxed_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_340_; 
v___x_340_ = 171;
return v___x_340_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_341_; 
v___x_341_ = 187;
return v___x_341_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_342_){
_start:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 171;
v___x_344_ = lean_uint32_dec_eq(v_c_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_345_){
_start:
{
uint32_t v_c_boxed_346_; uint8_t v_res_347_; lean_object* v_r_348_; 
v_c_boxed_346_ = lean_unbox_uint32(v_c_345_);
lean_dec(v_c_345_);
v_res_347_ = l_Lean_isIdBeginEscape(v_c_boxed_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_349_){
_start:
{
uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 187;
v___x_351_ = lean_uint32_dec_eq(v_c_349_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_352_){
_start:
{
uint32_t v_c_boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v_c_boxed_353_ = lean_unbox_uint32(v_c_352_);
lean_dec(v_c_352_);
v_res_354_ = l_Lean_isIdEndEscape(v_c_boxed_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
return v_x_356_;
}
else
{
lean_object* v_pre_357_; 
v_pre_357_ = lean_ctor_get(v_x_356_, 0);
if (lean_obj_tag(v_pre_357_) == 0)
{
lean_inc(v_x_356_);
return v_x_356_;
}
else
{
v_x_356_ = v_pre_357_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Name_getRoot(v_x_359_);
lean_dec(v_x_359_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_362_){
_start:
{
switch(lean_obj_tag(v_x_362_))
{
case 1:
{
lean_object* v_str_363_; uint32_t v___x_364_; uint8_t v___x_365_; 
v_str_363_ = lean_ctor_get(v_x_362_, 1);
lean_inc_ref_n(v_str_363_, 2);
lean_dec_ref_known(v_x_362_, 2);
v___x_364_ = 10013;
v___x_365_ = lean_string_contains(v_str_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_367_ = lean_string_dec_eq(v_str_363_, v___x_366_);
lean_dec_ref(v_str_363_);
return v___x_367_;
}
else
{
lean_dec_ref(v_str_363_);
return v___x_365_;
}
}
case 2:
{
lean_object* v_pre_368_; 
v_pre_368_ = lean_ctor_get(v_x_362_, 0);
lean_inc(v_pre_368_);
lean_dec_ref_known(v_x_362_, 2);
v_x_362_ = v_pre_368_;
goto _start;
}
default: 
{
uint8_t v___x_370_; 
lean_dec(v_x_362_);
v___x_370_ = 0;
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_Name_isInaccessibleUserName(v_x_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_374_, lean_object* v_i_375_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_string_utf8_byte_size(v_s_374_);
v___x_381_ = lean_nat_dec_lt(v_i_375_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
lean_dec(v_i_375_);
v___x_382_ = 1;
return v___x_382_;
}
else
{
uint8_t v_c_383_; uint8_t v___x_403_; uint8_t v___x_404_; 
lean_inc(v_i_375_);
v_c_383_ = lean_string_get_byte_fast(v_s_374_, v_i_375_);
v___x_403_ = 97;
v___x_404_ = lean_uint8_dec_le(v___x_403_, v_c_383_);
if (v___x_404_ == 0)
{
goto v___jp_398_;
}
else
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 122;
v___x_406_ = lean_uint8_dec_le(v_c_383_, v___x_405_);
if (v___x_406_ == 0)
{
goto v___jp_398_;
}
else
{
goto v___jp_376_;
}
}
v___jp_384_:
{
uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 95;
v___x_386_ = lean_uint8_dec_eq(v_c_383_, v___x_385_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 39;
v___x_388_ = lean_uint8_dec_eq(v_c_383_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 33;
v___x_390_ = lean_uint8_dec_eq(v_c_383_, v___x_389_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 63;
v___x_392_ = lean_uint8_dec_eq(v_c_383_, v___x_391_);
if (v___x_392_ == 0)
{
lean_dec(v_i_375_);
return v___x_392_;
}
else
{
goto v___jp_376_;
}
}
else
{
goto v___jp_376_;
}
}
else
{
goto v___jp_376_;
}
}
else
{
goto v___jp_376_;
}
}
v___jp_393_:
{
uint8_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 48;
v___x_395_ = lean_uint8_dec_le(v___x_394_, v_c_383_);
if (v___x_395_ == 0)
{
goto v___jp_384_;
}
else
{
uint8_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 57;
v___x_397_ = lean_uint8_dec_le(v_c_383_, v___x_396_);
if (v___x_397_ == 0)
{
goto v___jp_384_;
}
else
{
goto v___jp_376_;
}
}
}
v___jp_398_:
{
uint8_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 65;
v___x_400_ = lean_uint8_dec_le(v___x_399_, v_c_383_);
if (v___x_400_ == 0)
{
goto v___jp_393_;
}
else
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 90;
v___x_402_ = lean_uint8_dec_le(v_c_383_, v___x_401_);
if (v___x_402_ == 0)
{
goto v___jp_393_;
}
else
{
goto v___jp_376_;
}
}
}
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_i_375_, v___x_377_);
lean_dec(v_i_375_);
v_i_375_ = v___x_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_407_, lean_object* v_i_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_407_, v_i_408_);
lean_dec_ref(v_s_407_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_411_){
_start:
{
lean_object* v___x_415_; uint8_t v_c_416_; uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v_c_416_ = lean_string_get_byte_fast(v_s_411_, v___x_415_);
v___x_425_ = 97;
v___x_426_ = lean_uint8_dec_le(v___x_425_, v_c_416_);
if (v___x_426_ == 0)
{
goto v___jp_420_;
}
else
{
uint8_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 122;
v___x_428_ = lean_uint8_dec_le(v_c_416_, v___x_427_);
if (v___x_428_ == 0)
{
goto v___jp_420_;
}
else
{
goto v___jp_412_;
}
}
v___jp_412_:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_411_, v___x_413_);
return v___x_414_;
}
v___jp_417_:
{
uint8_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 95;
v___x_419_ = lean_uint8_dec_eq(v_c_416_, v___x_418_);
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
goto v___jp_412_;
}
}
v___jp_420_:
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 65;
v___x_422_ = lean_uint8_dec_le(v___x_421_, v_c_416_);
if (v___x_422_ == 0)
{
goto v___jp_417_;
}
else
{
uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 90;
v___x_424_ = lean_uint8_dec_le(v_c_416_, v___x_423_);
if (v___x_424_ == 0)
{
goto v___jp_417_;
}
else
{
goto v___jp_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_429_);
lean_dec_ref(v_s_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_432_, lean_object* v_h_433_){
_start:
{
lean_object* v___x_437_; uint8_t v_c_438_; uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v_c_438_ = lean_string_get_byte_fast(v_s_432_, v___x_437_);
v___x_447_ = 97;
v___x_448_ = lean_uint8_dec_le(v___x_447_, v_c_438_);
if (v___x_448_ == 0)
{
goto v___jp_442_;
}
else
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 122;
v___x_450_ = lean_uint8_dec_le(v_c_438_, v___x_449_);
if (v___x_450_ == 0)
{
goto v___jp_442_;
}
else
{
goto v___jp_434_;
}
}
v___jp_434_:
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_432_, v___x_435_);
return v___x_436_;
}
v___jp_439_:
{
uint8_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 95;
v___x_441_ = lean_uint8_dec_eq(v_c_438_, v___x_440_);
if (v___x_441_ == 0)
{
return v___x_441_;
}
else
{
goto v___jp_434_;
}
}
v___jp_442_:
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 65;
v___x_444_ = lean_uint8_dec_le(v___x_443_, v_c_438_);
if (v___x_444_ == 0)
{
goto v___jp_439_;
}
else
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 90;
v___x_446_ = lean_uint8_dec_le(v_c_438_, v___x_445_);
if (v___x_446_ == 0)
{
goto v___jp_439_;
}
else
{
goto v___jp_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_451_, lean_object* v_h_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_451_, v_h_452_);
lean_dec_ref(v_s_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_456_){
_start:
{
uint32_t v___y_466_; uint32_t v___y_471_; uint8_t v___y_472_; lean_object* v___x_487_; uint8_t v_c_488_; uint8_t v___x_497_; uint8_t v___x_498_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v_c_488_ = lean_string_get_byte_fast(v_s_456_, v___x_487_);
v___x_497_ = 97;
v___x_498_ = lean_uint8_dec_le(v___x_497_, v_c_488_);
if (v___x_498_ == 0)
{
goto v___jp_492_;
}
else
{
uint8_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = 122;
v___x_500_ = lean_uint8_dec_le(v_c_488_, v___x_499_);
if (v___x_500_ == 0)
{
goto v___jp_492_;
}
else
{
goto v___jp_484_;
}
}
v___jp_457_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_string_utf8_byte_size(v_s_456_);
v___x_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_460_, 0, v_s_456_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_substring_drop(v___x_460_, v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_464_ = lean_substring_all(v___x_462_, v___x_463_);
return v___x_464_;
}
v___jp_465_:
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 95;
v___x_468_ = lean_uint32_dec_eq(v___y_466_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_isLetterLike(v___y_466_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_s_456_);
return v___x_469_;
}
else
{
goto v___jp_457_;
}
}
else
{
goto v___jp_457_;
}
}
v___jp_470_:
{
if (v___y_472_ == 0)
{
uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 97;
v___x_474_ = lean_uint32_dec_le(v___x_473_, v___y_471_);
if (v___x_474_ == 0)
{
v___y_466_ = v___y_471_;
goto v___jp_465_;
}
else
{
uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 122;
v___x_476_ = lean_uint32_dec_le(v___y_471_, v___x_475_);
if (v___x_476_ == 0)
{
v___y_466_ = v___y_471_;
goto v___jp_465_;
}
else
{
goto v___jp_457_;
}
}
}
else
{
goto v___jp_457_;
}
}
v___jp_477_:
{
lean_object* v___x_478_; uint32_t v___x_479_; uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_string_utf8_get(v_s_456_, v___x_478_);
v___x_480_ = 65;
v___x_481_ = lean_uint32_dec_le(v___x_480_, v___x_479_);
if (v___x_481_ == 0)
{
v___y_471_ = v___x_479_;
v___y_472_ = v___x_481_;
goto v___jp_470_;
}
else
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 90;
v___x_483_ = lean_uint32_dec_le(v___x_479_, v___x_482_);
v___y_471_ = v___x_479_;
v___y_472_ = v___x_483_;
goto v___jp_470_;
}
}
v___jp_484_:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_456_, v___x_485_);
if (v___x_486_ == 0)
{
goto v___jp_477_;
}
else
{
lean_dec_ref(v_s_456_);
return v___x_486_;
}
}
v___jp_489_:
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 95;
v___x_491_ = lean_uint8_dec_eq(v_c_488_, v___x_490_);
if (v___x_491_ == 0)
{
goto v___jp_477_;
}
else
{
goto v___jp_484_;
}
}
v___jp_492_:
{
uint8_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 65;
v___x_494_ = lean_uint8_dec_le(v___x_493_, v_c_488_);
if (v___x_494_ == 0)
{
goto v___jp_489_;
}
else
{
uint8_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 90;
v___x_496_ = lean_uint8_dec_le(v_c_488_, v___x_495_);
if (v___x_496_ == 0)
{
goto v___jp_489_;
}
else
{
goto v___jp_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_504_, lean_object* v_h_505_){
_start:
{
uint32_t v___y_515_; uint32_t v___y_520_; uint8_t v___y_521_; lean_object* v___x_536_; uint8_t v_c_537_; uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v_c_537_ = lean_string_get_byte_fast(v_s_504_, v___x_536_);
v___x_546_ = 97;
v___x_547_ = lean_uint8_dec_le(v___x_546_, v_c_537_);
if (v___x_547_ == 0)
{
goto v___jp_541_;
}
else
{
uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = 122;
v___x_549_ = lean_uint8_dec_le(v_c_537_, v___x_548_);
if (v___x_549_ == 0)
{
goto v___jp_541_;
}
else
{
goto v___jp_533_;
}
}
v___jp_506_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_string_utf8_byte_size(v_s_504_);
v___x_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_509_, 0, v_s_504_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_508_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_substring_drop(v___x_509_, v___x_510_);
v___x_512_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_513_ = lean_substring_all(v___x_511_, v___x_512_);
return v___x_513_;
}
v___jp_514_:
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 95;
v___x_517_ = lean_uint32_dec_eq(v___y_515_, v___x_516_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_isLetterLike(v___y_515_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_s_504_);
return v___x_518_;
}
else
{
goto v___jp_506_;
}
}
else
{
goto v___jp_506_;
}
}
v___jp_519_:
{
if (v___y_521_ == 0)
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 97;
v___x_523_ = lean_uint32_dec_le(v___x_522_, v___y_520_);
if (v___x_523_ == 0)
{
v___y_515_ = v___y_520_;
goto v___jp_514_;
}
else
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 122;
v___x_525_ = lean_uint32_dec_le(v___y_520_, v___x_524_);
if (v___x_525_ == 0)
{
v___y_515_ = v___y_520_;
goto v___jp_514_;
}
else
{
goto v___jp_506_;
}
}
}
else
{
goto v___jp_506_;
}
}
v___jp_526_:
{
lean_object* v___x_527_; uint32_t v___x_528_; uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_string_utf8_get(v_s_504_, v___x_527_);
v___x_529_ = 65;
v___x_530_ = lean_uint32_dec_le(v___x_529_, v___x_528_);
if (v___x_530_ == 0)
{
v___y_520_ = v___x_528_;
v___y_521_ = v___x_530_;
goto v___jp_519_;
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 90;
v___x_532_ = lean_uint32_dec_le(v___x_528_, v___x_531_);
v___y_520_ = v___x_528_;
v___y_521_ = v___x_532_;
goto v___jp_519_;
}
}
v___jp_533_:
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_504_, v___x_534_);
if (v___x_535_ == 0)
{
goto v___jp_526_;
}
else
{
lean_dec_ref(v_s_504_);
return v___x_535_;
}
}
v___jp_538_:
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 95;
v___x_540_ = lean_uint8_dec_eq(v_c_537_, v___x_539_);
if (v___x_540_ == 0)
{
goto v___jp_526_;
}
else
{
goto v___jp_533_;
}
}
v___jp_541_:
{
uint8_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 65;
v___x_543_ = lean_uint8_dec_le(v___x_542_, v_c_537_);
if (v___x_543_ == 0)
{
goto v___jp_538_;
}
else
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 90;
v___x_545_ = lean_uint8_dec_le(v_c_537_, v___x_544_);
if (v___x_545_ == 0)
{
goto v___jp_538_;
}
else
{
goto v___jp_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_550_, lean_object* v_h_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_550_, v_h_551_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_558_ = lean_string_append(v___x_557_, v_s_556_);
v___x_559_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_560_ = lean_string_append(v___x_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_561_);
lean_dec_ref(v_s_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_564_, uint8_t v_force_565_){
_start:
{
uint8_t v___y_576_; uint32_t v___y_587_; uint32_t v___y_592_; uint8_t v___y_593_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_string_utf8_byte_size(v_s_564_);
v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_611_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_612_ = lean_string_append(v___x_611_, v_s_564_);
lean_dec_ref(v_s_564_);
v___x_613_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
else
{
if (v_force_565_ == 0)
{
uint8_t v_c_616_; uint8_t v___x_625_; uint8_t v___x_626_; 
v_c_616_ = lean_string_get_byte_fast(v_s_564_, v___x_608_);
v___x_625_ = 97;
v___x_626_ = lean_uint8_dec_le(v___x_625_, v_c_616_);
if (v___x_626_ == 0)
{
goto v___jp_620_;
}
else
{
uint8_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 122;
v___x_628_ = lean_uint8_dec_le(v_c_616_, v___x_627_);
if (v___x_628_ == 0)
{
goto v___jp_620_;
}
else
{
goto v___jp_605_;
}
}
v___jp_617_:
{
uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 95;
v___x_619_ = lean_uint8_dec_eq(v_c_616_, v___x_618_);
if (v___x_619_ == 0)
{
goto v___jp_598_;
}
else
{
goto v___jp_605_;
}
}
v___jp_620_:
{
uint8_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 65;
v___x_622_ = lean_uint8_dec_le(v___x_621_, v_c_616_);
if (v___x_622_ == 0)
{
goto v___jp_617_;
}
else
{
uint8_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 90;
v___x_624_ = lean_uint8_dec_le(v_c_616_, v___x_623_);
if (v___x_624_ == 0)
{
goto v___jp_617_;
}
else
{
goto v___jp_605_;
}
}
}
}
else
{
goto v___jp_566_;
}
}
v___jp_566_:
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_564_);
v___x_568_ = lean_string_any(v_s_564_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_570_ = lean_string_append(v___x_569_, v_s_564_);
lean_dec_ref(v_s_564_);
v___x_571_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; 
lean_dec_ref(v_s_564_);
v___x_574_ = lean_box(0);
return v___x_574_;
}
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
goto v___jp_566_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_s_564_);
return v___x_577_;
}
}
v___jp_578_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_string_utf8_byte_size(v_s_564_);
lean_inc_ref(v_s_564_);
v___x_581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_581_, 0, v_s_564_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_substring_drop(v___x_581_, v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_585_ = lean_substring_all(v___x_583_, v___x_584_);
v___y_576_ = v___x_585_;
goto v___jp_575_;
}
v___jp_586_:
{
uint32_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = 95;
v___x_589_ = lean_uint32_dec_eq(v___y_587_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_isLetterLike(v___y_587_);
if (v___x_590_ == 0)
{
v___y_576_ = v___x_590_;
goto v___jp_575_;
}
else
{
goto v___jp_578_;
}
}
else
{
goto v___jp_578_;
}
}
v___jp_591_:
{
if (v___y_593_ == 0)
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 97;
v___x_595_ = lean_uint32_dec_le(v___x_594_, v___y_592_);
if (v___x_595_ == 0)
{
v___y_587_ = v___y_592_;
goto v___jp_586_;
}
else
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 122;
v___x_597_ = lean_uint32_dec_le(v___y_592_, v___x_596_);
if (v___x_597_ == 0)
{
v___y_587_ = v___y_592_;
goto v___jp_586_;
}
else
{
goto v___jp_578_;
}
}
}
else
{
goto v___jp_578_;
}
}
v___jp_598_:
{
lean_object* v___x_599_; uint32_t v___x_600_; uint32_t v___x_601_; uint8_t v___x_602_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_string_utf8_get(v_s_564_, v___x_599_);
v___x_601_ = 65;
v___x_602_ = lean_uint32_dec_le(v___x_601_, v___x_600_);
if (v___x_602_ == 0)
{
v___y_592_ = v___x_600_;
v___y_593_ = v___x_602_;
goto v___jp_591_;
}
else
{
uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 90;
v___x_604_ = lean_uint32_dec_le(v___x_600_, v___x_603_);
v___y_592_ = v___x_600_;
v___y_593_ = v___x_604_;
goto v___jp_591_;
}
}
v___jp_605_:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_564_, v___x_606_);
if (v___x_607_ == 0)
{
goto v___jp_598_;
}
else
{
v___y_576_ = v___x_607_;
goto v___jp_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_629_, lean_object* v_force_630_){
_start:
{
uint8_t v_force_boxed_631_; lean_object* v_res_632_; 
v_force_boxed_631_ = lean_unbox(v_force_630_);
v_res_632_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_629_, v_force_boxed_631_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_633_){
_start:
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 187;
v___x_635_ = lean_uint32_dec_eq(v___y_633_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_636_){
_start:
{
uint32_t v___y_309__boxed_637_; uint8_t v_res_638_; lean_object* v_r_639_; 
v___y_309__boxed_637_ = lean_unbox_uint32(v___y_636_);
lean_dec(v___y_636_);
v_res_638_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_309__boxed_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_640_){
_start:
{
uint8_t v___y_658_; uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 65;
v___x_664_ = lean_uint32_dec_le(v___x_663_, v___y_640_);
if (v___x_664_ == 0)
{
v___y_658_ = v___x_664_;
goto v___jp_657_;
}
else
{
uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 90;
v___x_666_ = lean_uint32_dec_le(v___y_640_, v___x_665_);
v___y_658_ = v___x_666_;
goto v___jp_657_;
}
v___jp_641_:
{
uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 95;
v___x_643_ = lean_uint32_dec_eq(v___y_640_, v___x_642_);
if (v___x_643_ == 0)
{
uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 39;
v___x_645_ = lean_uint32_dec_eq(v___y_640_, v___x_644_);
if (v___x_645_ == 0)
{
uint32_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 33;
v___x_647_ = lean_uint32_dec_eq(v___y_640_, v___x_646_);
if (v___x_647_ == 0)
{
uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 63;
v___x_649_ = lean_uint32_dec_eq(v___y_640_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_isLetterLike(v___y_640_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_isSubScriptAlnum(v___y_640_);
return v___x_651_;
}
else
{
return v___x_650_;
}
}
else
{
return v___x_649_;
}
}
else
{
return v___x_647_;
}
}
else
{
return v___x_645_;
}
}
else
{
return v___x_643_;
}
}
v___jp_652_:
{
uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 48;
v___x_654_ = lean_uint32_dec_le(v___x_653_, v___y_640_);
if (v___x_654_ == 0)
{
goto v___jp_641_;
}
else
{
uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 57;
v___x_656_ = lean_uint32_dec_le(v___y_640_, v___x_655_);
if (v___x_656_ == 0)
{
goto v___jp_641_;
}
else
{
return v___x_656_;
}
}
}
v___jp_657_:
{
if (v___y_658_ == 0)
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 97;
v___x_660_ = lean_uint32_dec_le(v___x_659_, v___y_640_);
if (v___x_660_ == 0)
{
goto v___jp_652_;
}
else
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 122;
v___x_662_ = lean_uint32_dec_le(v___y_640_, v___x_661_);
if (v___x_662_ == 0)
{
goto v___jp_652_;
}
else
{
return v___x_662_;
}
}
}
else
{
return v___y_658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_667_){
_start:
{
uint32_t v___y_316__boxed_668_; uint8_t v_res_669_; lean_object* v_r_670_; 
v___y_316__boxed_668_ = lean_unbox_uint32(v___y_667_);
lean_dec(v___y_667_);
v_res_669_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_316__boxed_668_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_673_, lean_object* v_s_674_, uint8_t v_force_675_){
_start:
{
if (v_escape_673_ == 0)
{
return v_s_674_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_string_utf8_byte_size(v_s_674_);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_680_ = lean_string_append(v___x_679_, v_s_674_);
lean_dec_ref(v_s_674_);
v___x_681_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v___f_683_; uint8_t v___y_691_; 
v___f_683_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_675_ == 0)
{
lean_object* v___f_692_; uint32_t v___y_699_; uint32_t v___y_704_; uint8_t v___y_705_; uint8_t v_c_719_; uint8_t v___x_728_; uint8_t v___x_729_; 
v___f_692_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_719_ = lean_string_get_byte_fast(v_s_674_, v___x_676_);
v___x_728_ = 97;
v___x_729_ = lean_uint8_dec_le(v___x_728_, v_c_719_);
if (v___x_729_ == 0)
{
goto v___jp_723_;
}
else
{
uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 122;
v___x_731_ = lean_uint8_dec_le(v_c_719_, v___x_730_);
if (v___x_731_ == 0)
{
goto v___jp_723_;
}
else
{
goto v___jp_716_;
}
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
lean_inc_ref(v_s_674_);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v_s_674_);
lean_ctor_set(v___x_694_, 1, v___x_676_);
lean_ctor_set(v___x_694_, 2, v___x_677_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_substring_drop(v___x_694_, v___x_695_);
v___x_697_ = lean_substring_all(v___x_696_, v___f_692_);
v___y_691_ = v___x_697_;
goto v___jp_690_;
}
v___jp_698_:
{
uint32_t v___x_700_; uint8_t v___x_701_; 
v___x_700_ = 95;
v___x_701_ = lean_uint32_dec_eq(v___y_699_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_isLetterLike(v___y_699_);
if (v___x_702_ == 0)
{
v___y_691_ = v___x_702_;
goto v___jp_690_;
}
else
{
goto v___jp_693_;
}
}
else
{
goto v___jp_693_;
}
}
v___jp_703_:
{
if (v___y_705_ == 0)
{
uint32_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = 97;
v___x_707_ = lean_uint32_dec_le(v___x_706_, v___y_704_);
if (v___x_707_ == 0)
{
v___y_699_ = v___y_704_;
goto v___jp_698_;
}
else
{
uint32_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 122;
v___x_709_ = lean_uint32_dec_le(v___y_704_, v___x_708_);
if (v___x_709_ == 0)
{
v___y_699_ = v___y_704_;
goto v___jp_698_;
}
else
{
goto v___jp_693_;
}
}
}
else
{
goto v___jp_693_;
}
}
v___jp_710_:
{
uint32_t v___x_711_; uint32_t v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_string_utf8_get(v_s_674_, v___x_676_);
v___x_712_ = 65;
v___x_713_ = lean_uint32_dec_le(v___x_712_, v___x_711_);
if (v___x_713_ == 0)
{
v___y_704_ = v___x_711_;
v___y_705_ = v___x_713_;
goto v___jp_703_;
}
else
{
uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 90;
v___x_715_ = lean_uint32_dec_le(v___x_711_, v___x_714_);
v___y_704_ = v___x_711_;
v___y_705_ = v___x_715_;
goto v___jp_703_;
}
}
v___jp_716_:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_674_, v___x_717_);
if (v___x_718_ == 0)
{
goto v___jp_710_;
}
else
{
v___y_691_ = v___x_718_;
goto v___jp_690_;
}
}
v___jp_720_:
{
uint8_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = 95;
v___x_722_ = lean_uint8_dec_eq(v_c_719_, v___x_721_);
if (v___x_722_ == 0)
{
goto v___jp_710_;
}
else
{
goto v___jp_716_;
}
}
v___jp_723_:
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 65;
v___x_725_ = lean_uint8_dec_le(v___x_724_, v_c_719_);
if (v___x_725_ == 0)
{
goto v___jp_720_;
}
else
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 90;
v___x_727_ = lean_uint8_dec_le(v_c_719_, v___x_726_);
if (v___x_727_ == 0)
{
goto v___jp_720_;
}
else
{
goto v___jp_716_;
}
}
}
}
else
{
goto v___jp_684_;
}
v___jp_684_:
{
uint8_t v___x_685_; 
lean_inc_ref(v_s_674_);
v___x_685_ = lean_string_any(v_s_674_, v___f_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_687_ = lean_string_append(v___x_686_, v_s_674_);
lean_dec_ref(v_s_674_);
v___x_688_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
return v___x_689_;
}
else
{
return v_s_674_;
}
}
v___jp_690_:
{
if (v___y_691_ == 0)
{
goto v___jp_684_;
}
else
{
return v_s_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_732_, lean_object* v_s_733_, lean_object* v_force_734_){
_start:
{
uint8_t v_escape_boxed_735_; uint8_t v_force_boxed_736_; lean_object* v_res_737_; 
v_escape_boxed_735_ = lean_unbox(v_escape_732_);
v_force_boxed_736_ = lean_unbox(v_force_734_);
v_res_737_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_735_, v_s_733_, v_force_boxed_736_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = 0;
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_740_);
lean_dec_ref(v_x_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_745_, uint8_t v_escape_746_, lean_object* v_n_747_, lean_object* v_isToken_748_){
_start:
{
switch(lean_obj_tag(v_n_747_))
{
case 0:
{
lean_object* v___x_749_; 
lean_dec_ref(v_isToken_748_);
v___x_749_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_749_;
}
case 1:
{
lean_object* v_pre_750_; 
v_pre_750_ = lean_ctor_get(v_n_747_, 0);
if (lean_obj_tag(v_pre_750_) == 0)
{
lean_object* v_str_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; 
v_str_751_ = lean_ctor_get(v_n_747_, 1);
lean_inc_ref_n(v_str_751_, 2);
lean_dec_ref_known(v_n_747_, 2);
v___x_752_ = lean_apply_1(v_isToken_748_, v_str_751_);
v___x_753_ = lean_unbox(v___x_752_);
v___x_754_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_746_, v_str_751_, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v_str_755_; lean_object* v_r_756_; lean_object* v___x_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v_r_x27_760_; 
lean_inc(v_pre_750_);
v_str_755_ = lean_ctor_get(v_n_747_, 1);
lean_inc_ref_n(v_str_755_, 2);
lean_dec_ref_known(v_n_747_, 2);
lean_inc_ref(v_isToken_748_);
v_r_756_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_745_, v_escape_746_, v_pre_750_, v_isToken_748_);
v___x_757_ = lean_string_append(v_r_756_, v_sep_745_);
v___x_758_ = 0;
v___x_759_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_746_, v_str_755_, v___x_758_);
lean_inc_ref(v___x_757_);
v_r_x27_760_ = lean_string_append(v___x_757_, v___x_759_);
lean_dec_ref(v___x_759_);
if (v_escape_746_ == 0)
{
lean_dec_ref(v___x_757_);
lean_dec_ref(v_str_755_);
lean_dec_ref(v_isToken_748_);
return v_r_x27_760_;
}
else
{
lean_object* v___x_761_; uint8_t v___x_762_; 
lean_inc_ref(v_r_x27_760_);
v___x_761_ = lean_apply_1(v_isToken_748_, v_r_x27_760_);
v___x_762_ = lean_unbox(v___x_761_);
if (v___x_762_ == 0)
{
lean_dec_ref(v___x_757_);
lean_dec_ref(v_str_755_);
return v_r_x27_760_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v_r_x27_760_);
v___x_763_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_746_, v_str_755_, v_escape_746_);
v___x_764_ = lean_string_append(v___x_757_, v___x_763_);
lean_dec_ref(v___x_763_);
return v___x_764_;
}
}
}
}
default: 
{
lean_object* v_pre_765_; 
lean_dec_ref(v_isToken_748_);
v_pre_765_ = lean_ctor_get(v_n_747_, 0);
if (lean_obj_tag(v_pre_765_) == 0)
{
lean_object* v_i_766_; lean_object* v___x_767_; 
v_i_766_ = lean_ctor_get(v_n_747_, 1);
lean_inc(v_i_766_);
lean_dec_ref_known(v_n_747_, 2);
v___x_767_ = l_Nat_reprFast(v_i_766_);
return v___x_767_;
}
else
{
lean_object* v_i_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_inc(v_pre_765_);
v_i_768_ = lean_ctor_get(v_n_747_, 1);
lean_inc(v_i_768_);
lean_dec_ref_known(v_n_747_, 2);
v___f_769_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_770_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_745_, v_escape_746_, v_pre_765_, v___f_769_);
v___x_771_ = lean_string_append(v___x_770_, v_sep_745_);
v___x_772_ = l_Nat_reprFast(v_i_768_);
v___x_773_ = lean_string_append(v___x_771_, v___x_772_);
lean_dec_ref(v___x_772_);
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_774_, lean_object* v_escape_775_, lean_object* v_n_776_, lean_object* v_isToken_777_){
_start:
{
uint8_t v_escape_boxed_778_; lean_object* v_res_779_; 
v_escape_boxed_778_ = lean_unbox(v_escape_775_);
v_res_779_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_774_, v_escape_boxed_778_, v_n_776_, v_isToken_777_);
lean_dec_ref(v_sep_774_);
return v_res_779_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_785_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; uint8_t v___x_788_; 
v___x_786_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_787_ = lean_name_eq(v_n_785_, v___x_786_);
v___x_788_ = 1;
if (v___x_787_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Name_getRoot(v_n_785_);
if (lean_obj_tag(v___x_789_) == 1)
{
lean_object* v_str_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_str_790_ = lean_ctor_get(v___x_789_, 1);
lean_inc_ref_n(v_str_790_, 2);
lean_dec_ref_known(v___x_789_, 2);
v___x_791_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_792_ = lean_string_isprefixof(v___x_791_, v_str_790_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_794_ = lean_string_isprefixof(v___x_793_, v_str_790_);
return v___x_794_;
}
else
{
lean_dec_ref(v_str_790_);
return v___x_788_;
}
}
else
{
lean_dec(v___x_789_);
return v___x_787_;
}
}
else
{
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_795_);
lean_dec(v_n_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_798_, uint8_t v_escape_799_, lean_object* v_isToken_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_799_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_801_, v_escape_799_, v_n_798_, v_isToken_800_);
return v___x_802_;
}
else
{
uint8_t v___x_803_; 
lean_inc(v_n_798_);
v___x_803_ = l_Lean_Name_isInaccessibleUserName(v_n_798_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = l_Lean_Name_hasMacroScopes(v_n_798_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
v___x_805_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_798_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_801_, v_escape_799_, v_n_798_, v_isToken_800_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_801_, v___x_804_, v_n_798_, v_isToken_800_);
return v___x_807_;
}
}
else
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_801_, v___x_803_, v_n_798_, v_isToken_800_);
return v___x_808_;
}
}
else
{
uint8_t v___x_809_; lean_object* v___x_810_; 
v___x_809_ = 0;
v___x_810_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_801_, v___x_809_, v_n_798_, v_isToken_800_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_811_, lean_object* v_escape_812_, lean_object* v_isToken_813_){
_start:
{
uint8_t v_escape_boxed_814_; lean_object* v_res_815_; 
v_escape_boxed_814_ = lean_unbox(v_escape_812_);
v_res_815_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_811_, v_escape_boxed_814_, v_isToken_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_816_, uint8_t v_escape_817_, lean_object* v_n_818_){
_start:
{
switch(lean_obj_tag(v_n_818_))
{
case 0:
{
lean_object* v___x_819_; 
v___x_819_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_819_;
}
case 1:
{
lean_object* v_pre_820_; 
v_pre_820_ = lean_ctor_get(v_n_818_, 0);
if (lean_obj_tag(v_pre_820_) == 0)
{
lean_object* v_str_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v_str_821_ = lean_ctor_get(v_n_818_, 1);
lean_inc_ref(v_str_821_);
lean_dec_ref_known(v_n_818_, 2);
v___x_822_ = 0;
v___x_823_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_817_, v_str_821_, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_str_824_; lean_object* v_r_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v_r_x27_829_; 
lean_inc(v_pre_820_);
v_str_824_ = lean_ctor_get(v_n_818_, 1);
lean_inc_ref(v_str_824_);
lean_dec_ref_known(v_n_818_, 2);
v_r_825_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_816_, v_escape_817_, v_pre_820_);
v___x_826_ = lean_string_append(v_r_825_, v_sep_816_);
v___x_827_ = 0;
v___x_828_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_817_, v_str_824_, v___x_827_);
v_r_x27_829_ = lean_string_append(v___x_826_, v___x_828_);
lean_dec_ref(v___x_828_);
return v_r_x27_829_;
}
}
default: 
{
lean_object* v_pre_830_; 
v_pre_830_ = lean_ctor_get(v_n_818_, 0);
if (lean_obj_tag(v_pre_830_) == 0)
{
lean_object* v_i_831_; lean_object* v___x_832_; 
v_i_831_ = lean_ctor_get(v_n_818_, 1);
lean_inc(v_i_831_);
lean_dec_ref_known(v_n_818_, 2);
v___x_832_ = l_Nat_reprFast(v_i_831_);
return v___x_832_;
}
else
{
lean_object* v_i_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_inc(v_pre_830_);
v_i_833_ = lean_ctor_get(v_n_818_, 1);
lean_inc(v_i_833_);
lean_dec_ref_known(v_n_818_, 2);
v___x_834_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_816_, v_escape_817_, v_pre_830_);
v___x_835_ = lean_string_append(v___x_834_, v_sep_816_);
v___x_836_ = l_Nat_reprFast(v_i_833_);
v___x_837_ = lean_string_append(v___x_835_, v___x_836_);
lean_dec_ref(v___x_836_);
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_838_, lean_object* v_escape_839_, lean_object* v_n_840_){
_start:
{
uint8_t v_escape_boxed_841_; lean_object* v_res_842_; 
v_escape_boxed_841_ = lean_unbox(v_escape_839_);
v_res_842_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_838_, v_escape_boxed_841_, v_n_840_);
lean_dec_ref(v_sep_838_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_843_, uint8_t v_escape_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_844_ == 0)
{
lean_object* v___x_846_; 
v___x_846_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_845_, v_escape_844_, v_n_843_);
return v___x_846_;
}
else
{
uint8_t v___x_847_; 
lean_inc(v_n_843_);
v___x_847_ = l_Lean_Name_isInaccessibleUserName(v_n_843_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_Name_hasMacroScopes(v_n_843_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; 
v___x_849_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_843_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_845_, v_escape_844_, v_n_843_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_845_, v___x_848_, v_n_843_);
return v___x_851_;
}
}
else
{
lean_object* v___x_852_; 
v___x_852_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_845_, v___x_847_, v_n_843_);
return v___x_852_;
}
}
else
{
uint8_t v___x_853_; lean_object* v___x_854_; 
v___x_853_ = 0;
v___x_854_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_845_, v___x_853_, v_n_843_);
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_855_, lean_object* v_escape_856_){
_start:
{
uint8_t v_escape_boxed_857_; lean_object* v_res_858_; 
v_escape_boxed_857_ = lean_unbox(v_escape_856_);
v_res_858_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_855_, v_escape_boxed_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_859_, uint8_t v_escape_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_859_, v_escape_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_862_, lean_object* v_escape_863_){
_start:
{
uint8_t v_escape_boxed_864_; lean_object* v_res_865_; 
v_escape_boxed_864_ = lean_unbox(v_escape_863_);
v_res_865_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_862_, v_escape_boxed_864_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_866_){
_start:
{
switch(lean_obj_tag(v_x_866_))
{
case 0:
{
uint8_t v___x_867_; 
v___x_867_ = 0;
return v___x_867_;
}
case 1:
{
lean_object* v_pre_868_; 
v_pre_868_ = lean_ctor_get(v_x_866_, 0);
v_x_866_ = v_pre_868_;
goto _start;
}
default: 
{
uint8_t v___x_870_; 
v___x_870_ = 1;
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_871_);
lean_dec(v_x_871_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_889_, lean_object* v_prec_890_){
_start:
{
switch(lean_obj_tag(v_n_889_))
{
case 0:
{
lean_object* v___x_891_; 
v___x_891_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_891_;
}
case 1:
{
lean_object* v_pre_892_; lean_object* v_str_893_; uint8_t v___x_894_; 
v_pre_892_ = lean_ctor_get(v_n_889_, 0);
v_str_893_ = lean_ctor_get(v_n_889_, 1);
v___x_894_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_892_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_895_ = 1;
v___x_896_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_897_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_889_, v___x_895_);
v___x_898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_inc_ref(v_str_893_);
lean_inc(v_pre_892_);
lean_dec_ref_known(v_n_889_, 2);
v___x_900_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_901_ = lean_unsigned_to_nat(1024u);
v___x_902_ = l_Lean_Name_reprPrec(v_pre_892_, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_900_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_String_quote(v_str_893_);
v___x_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_905_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Repr_addAppParen(v___x_908_, v_prec_890_);
return v___x_909_;
}
}
default: 
{
lean_object* v_pre_910_; lean_object* v_i_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_pre_910_ = lean_ctor_get(v_n_889_, 0);
lean_inc(v_pre_910_);
v_i_911_ = lean_ctor_get(v_n_889_, 1);
lean_inc(v_i_911_);
lean_dec_ref_known(v_n_889_, 2);
v___x_912_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_913_ = lean_unsigned_to_nat(1024u);
v___x_914_ = l_Lean_Name_reprPrec(v_pre_910_, v___x_913_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_912_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Nat_reprFast(v_i_911_);
v___x_919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_917_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Repr_addAppParen(v___x_920_, v_prec_890_);
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_922_, lean_object* v_prec_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Name_reprPrec(v_n_922_, v_prec_923_);
lean_dec(v_prec_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_927_){
_start:
{
if (lean_obj_tag(v_x_927_) == 1)
{
lean_object* v_pre_928_; lean_object* v_str_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_pre_928_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_pre_928_);
v_str_929_ = lean_ctor_get(v_x_927_, 1);
lean_inc_ref(v_str_929_);
lean_dec_ref_known(v_x_927_, 2);
v___x_930_ = lean_string_capitalize(v_str_929_);
v___x_931_ = l_Lean_Name_str___override(v_pre_928_, v___x_930_);
return v___x_931_;
}
else
{
return v_x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
switch(lean_obj_tag(v_x_932_))
{
case 0:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_inc(v_x_934_);
return v_x_934_;
}
else
{
return v_x_932_;
}
}
case 1:
{
lean_object* v_pre_935_; lean_object* v_str_936_; uint8_t v___x_937_; 
v_pre_935_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_pre_935_);
v_str_936_ = lean_ctor_get(v_x_932_, 1);
lean_inc_ref(v_str_936_);
v___x_937_ = lean_name_eq(v_x_932_, v_x_933_);
lean_dec_ref_known(v_x_932_, 2);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = l_Lean_Name_replacePrefix(v_pre_935_, v_x_933_, v_x_934_);
v___x_939_ = l_Lean_Name_str___override(v___x_938_, v_str_936_);
return v___x_939_;
}
else
{
lean_dec_ref(v_str_936_);
lean_dec(v_pre_935_);
lean_inc(v_x_934_);
return v_x_934_;
}
}
default: 
{
lean_object* v_pre_940_; lean_object* v_i_941_; uint8_t v___x_942_; 
v_pre_940_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_pre_940_);
v_i_941_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_i_941_);
v___x_942_ = lean_name_eq(v_x_932_, v_x_933_);
lean_dec_ref_known(v_x_932_, 2);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = l_Lean_Name_replacePrefix(v_pre_940_, v_x_933_, v_x_934_);
v___x_944_ = l_Lean_Name_num___override(v___x_943_, v_i_941_);
return v___x_944_;
}
else
{
lean_dec(v_i_941_);
lean_dec(v_pre_940_);
lean_inc(v_x_934_);
return v_x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Name_replacePrefix(v_x_945_, v_x_946_, v_x_947_);
lean_dec(v_x_947_);
lean_dec(v_x_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
switch(lean_obj_tag(v_x_950_))
{
case 0:
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_x_949_);
return v___x_951_;
}
case 1:
{
if (lean_obj_tag(v_x_949_) == 1)
{
lean_object* v_pre_952_; lean_object* v_str_953_; lean_object* v_pre_954_; lean_object* v_str_955_; uint8_t v___x_956_; 
v_pre_952_ = lean_ctor_get(v_x_950_, 0);
v_str_953_ = lean_ctor_get(v_x_950_, 1);
v_pre_954_ = lean_ctor_get(v_x_949_, 0);
lean_inc(v_pre_954_);
v_str_955_ = lean_ctor_get(v_x_949_, 1);
lean_inc_ref(v_str_955_);
lean_dec_ref_known(v_x_949_, 2);
v___x_956_ = lean_string_dec_eq(v_str_955_, v_str_953_);
lean_dec_ref(v_str_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v_pre_954_);
v___x_957_ = lean_box(0);
return v___x_957_;
}
else
{
v_x_949_ = v_pre_954_;
v_x_950_ = v_pre_952_;
goto _start;
}
}
else
{
lean_object* v___x_959_; 
lean_dec(v_x_949_);
v___x_959_ = lean_box(0);
return v___x_959_;
}
}
default: 
{
if (lean_obj_tag(v_x_949_) == 2)
{
lean_object* v_pre_960_; lean_object* v_i_961_; lean_object* v_pre_962_; lean_object* v_i_963_; uint8_t v___x_964_; 
v_pre_960_ = lean_ctor_get(v_x_950_, 0);
v_i_961_ = lean_ctor_get(v_x_950_, 1);
v_pre_962_ = lean_ctor_get(v_x_949_, 0);
lean_inc(v_pre_962_);
v_i_963_ = lean_ctor_get(v_x_949_, 1);
lean_inc(v_i_963_);
lean_dec_ref_known(v_x_949_, 2);
v___x_964_ = lean_nat_dec_eq(v_i_963_, v_i_961_);
lean_dec(v_i_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
lean_dec(v_pre_962_);
v___x_965_ = lean_box(0);
return v___x_965_;
}
else
{
v_x_949_ = v_pre_962_;
v_x_950_ = v_pre_960_;
goto _start;
}
}
else
{
lean_object* v___x_967_; 
lean_dec(v_x_949_);
v___x_967_ = lean_box(0);
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Name_eraseSuffix_x3f(v_x_968_, v_x_969_);
lean_dec(v_x_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_971_, lean_object* v_f_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_Name_hasMacroScopes(v_n_971_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_apply_1(v_f_972_, v_n_971_);
return v___x_974_;
}
else
{
lean_object* v_view_975_; lean_object* v_name_976_; lean_object* v_imported_977_; lean_object* v_ctx_978_; lean_object* v_scopes_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_988_; 
v_view_975_ = l_Lean_extractMacroScopes(v_n_971_);
v_name_976_ = lean_ctor_get(v_view_975_, 0);
v_imported_977_ = lean_ctor_get(v_view_975_, 1);
v_ctx_978_ = lean_ctor_get(v_view_975_, 2);
v_scopes_979_ = lean_ctor_get(v_view_975_, 3);
v_isSharedCheck_988_ = !lean_is_exclusive(v_view_975_);
if (v_isSharedCheck_988_ == 0)
{
v___x_981_ = v_view_975_;
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_scopes_979_);
lean_inc(v_ctx_978_);
lean_inc(v_imported_977_);
lean_inc(v_name_976_);
lean_dec(v_view_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_apply_1(v_f_972_, v_name_976_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_imported_977_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_ctx_978_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_scopes_979_);
v___x_985_ = v_reuseFailAlloc_987_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_MacroScopesView_review(v___x_985_);
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_989_, lean_object* v_x_990_){
_start:
{
if (lean_obj_tag(v_x_990_) == 1)
{
lean_object* v_pre_991_; lean_object* v_str_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_pre_991_ = lean_ctor_get(v_x_990_, 0);
lean_inc(v_pre_991_);
v_str_992_ = lean_ctor_get(v_x_990_, 1);
lean_inc_ref(v_str_992_);
lean_dec_ref_known(v_x_990_, 2);
v___x_993_ = lean_string_append(v_str_992_, v_suffix_989_);
lean_dec_ref(v_suffix_989_);
v___x_994_ = l_Lean_Name_str___override(v_pre_991_, v___x_993_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Name_str___override(v_x_990_, v_suffix_989_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_996_, lean_object* v_suffix_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Name_hasMacroScopes(v_n_996_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Name_appendAfter___lam__0(v_suffix_997_, v_n_996_);
return v___x_999_;
}
else
{
lean_object* v_view_1000_; lean_object* v_name_1001_; lean_object* v_imported_1002_; lean_object* v_ctx_1003_; lean_object* v_scopes_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1013_; 
v_view_1000_ = l_Lean_extractMacroScopes(v_n_996_);
v_name_1001_ = lean_ctor_get(v_view_1000_, 0);
v_imported_1002_ = lean_ctor_get(v_view_1000_, 1);
v_ctx_1003_ = lean_ctor_get(v_view_1000_, 2);
v_scopes_1004_ = lean_ctor_get(v_view_1000_, 3);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_view_1000_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1006_ = v_view_1000_;
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_scopes_1004_);
lean_inc(v_ctx_1003_);
lean_inc(v_imported_1002_);
lean_inc(v_name_1001_);
lean_dec(v_view_1000_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = l_Lean_Name_appendAfter___lam__0(v_suffix_997_, v_name_1001_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_imported_1002_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_ctx_1003_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_scopes_1004_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_MacroScopesView_review(v___x_1010_);
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 1)
{
lean_object* v_pre_1016_; lean_object* v_str_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_pre_1016_ = lean_ctor_get(v_x_1015_, 0);
lean_inc(v_pre_1016_);
v_str_1017_ = lean_ctor_get(v_x_1015_, 1);
lean_inc_ref(v_str_1017_);
lean_dec_ref_known(v_x_1015_, 2);
v___x_1018_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1019_ = lean_string_append(v_str_1017_, v___x_1018_);
v___x_1020_ = l_Nat_reprFast(v_idx_1014_);
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = l_Lean_Name_str___override(v_pre_1016_, v___x_1021_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1024_ = l_Nat_reprFast(v_idx_1014_);
v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = l_Lean_Name_str___override(v_x_1015_, v___x_1025_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1027_, lean_object* v_idx_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Name_hasMacroScopes(v_n_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1028_, v_n_1027_);
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
v___x_1039_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1028_, v_name_1032_);
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
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1045_, lean_object* v_x_1046_){
_start:
{
switch(lean_obj_tag(v_x_1046_))
{
case 0:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Name_str___override(v_x_1046_, v_pre_1045_);
return v___x_1047_;
}
case 1:
{
lean_object* v_pre_1048_; lean_object* v_str_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_pre_1048_ = lean_ctor_get(v_x_1046_, 0);
lean_inc(v_pre_1048_);
v_str_1049_ = lean_ctor_get(v_x_1046_, 1);
lean_inc_ref(v_str_1049_);
lean_dec_ref_known(v_x_1046_, 2);
v___x_1050_ = lean_string_append(v_pre_1045_, v_str_1049_);
lean_dec_ref(v_str_1049_);
v___x_1051_ = l_Lean_Name_str___override(v_pre_1048_, v___x_1050_);
return v___x_1051_;
}
default: 
{
lean_object* v_pre_1052_; lean_object* v_i_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_pre_1052_ = lean_ctor_get(v_x_1046_, 0);
lean_inc(v_pre_1052_);
v_i_1053_ = lean_ctor_get(v_x_1046_, 1);
lean_inc(v_i_1053_);
lean_dec_ref_known(v_x_1046_, 2);
v___x_1054_ = l_Lean_Name_str___override(v_pre_1052_, v_pre_1045_);
v___x_1055_ = l_Lean_Name_num___override(v___x_1054_, v_i_1053_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore(lean_object* v_n_1056_, lean_object* v_pre_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Lean_Name_hasMacroScopes(v_n_1056_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Name_appendBefore___lam__0(v_pre_1057_, v_n_1056_);
return v___x_1059_;
}
else
{
lean_object* v_view_1060_; lean_object* v_name_1061_; lean_object* v_imported_1062_; lean_object* v_ctx_1063_; lean_object* v_scopes_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1073_; 
v_view_1060_ = l_Lean_extractMacroScopes(v_n_1056_);
v_name_1061_ = lean_ctor_get(v_view_1060_, 0);
v_imported_1062_ = lean_ctor_get(v_view_1060_, 1);
v_ctx_1063_ = lean_ctor_get(v_view_1060_, 2);
v_scopes_1064_ = lean_ctor_get(v_view_1060_, 3);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_view_1060_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1066_ = v_view_1060_;
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_scopes_1064_);
lean_inc(v_ctx_1063_);
lean_inc(v_imported_1062_);
lean_inc(v_name_1061_);
lean_dec(v_view_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_Name_appendBefore___lam__0(v_pre_1057_, v_name_1061_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_imported_1062_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_ctx_1063_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v_scopes_1064_);
v___x_1070_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_MacroScopesView_review(v___x_1070_);
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_h__1_1076_, lean_object* v_h__2_1077_, lean_object* v_h__3_1078_, lean_object* v_h__4_1079_){
_start:
{
switch(lean_obj_tag(v_x_1074_))
{
case 0:
{
lean_dec(v_h__3_1078_);
lean_dec(v_h__2_1077_);
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__4_1079_);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_apply_1(v_h__1_1076_, v___x_1080_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_h__1_1076_);
v___x_1082_ = lean_apply_5(v_h__4_1079_, v_x_1074_, v_x_1075_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1082_;
}
}
case 1:
{
lean_dec(v_h__3_1078_);
lean_dec(v_h__1_1076_);
if (lean_obj_tag(v_x_1075_) == 1)
{
lean_object* v_pre_1083_; lean_object* v_str_1084_; lean_object* v_pre_1085_; lean_object* v_str_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__4_1079_);
v_pre_1083_ = lean_ctor_get(v_x_1074_, 0);
lean_inc(v_pre_1083_);
v_str_1084_ = lean_ctor_get(v_x_1074_, 1);
lean_inc_ref(v_str_1084_);
lean_dec_ref_known(v_x_1074_, 2);
v_pre_1085_ = lean_ctor_get(v_x_1075_, 0);
lean_inc(v_pre_1085_);
v_str_1086_ = lean_ctor_get(v_x_1075_, 1);
lean_inc_ref(v_str_1086_);
lean_dec_ref_known(v_x_1075_, 2);
v___x_1087_ = lean_apply_4(v_h__2_1077_, v_pre_1083_, v_str_1084_, v_pre_1085_, v_str_1086_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_h__2_1077_);
v___x_1088_ = lean_apply_5(v_h__4_1079_, v_x_1074_, v_x_1075_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1088_;
}
}
default: 
{
lean_dec(v_h__2_1077_);
lean_dec(v_h__1_1076_);
if (lean_obj_tag(v_x_1075_) == 2)
{
lean_object* v_pre_1089_; lean_object* v_i_1090_; lean_object* v_pre_1091_; lean_object* v_i_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__4_1079_);
v_pre_1089_ = lean_ctor_get(v_x_1074_, 0);
lean_inc(v_pre_1089_);
v_i_1090_ = lean_ctor_get(v_x_1074_, 1);
lean_inc(v_i_1090_);
lean_dec_ref_known(v_x_1074_, 2);
v_pre_1091_ = lean_ctor_get(v_x_1075_, 0);
lean_inc(v_pre_1091_);
v_i_1092_ = lean_ctor_get(v_x_1075_, 1);
lean_inc(v_i_1092_);
lean_dec_ref_known(v_x_1075_, 2);
v___x_1093_ = lean_apply_4(v_h__3_1078_, v_pre_1089_, v_i_1090_, v_pre_1091_, v_i_1092_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_h__3_1078_);
v___x_1094_ = lean_apply_5(v_h__4_1079_, v_x_1074_, v_x_1075_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_h__1_1098_, lean_object* v_h__2_1099_, lean_object* v_h__3_1100_, lean_object* v_h__4_1101_){
_start:
{
switch(lean_obj_tag(v_x_1096_))
{
case 0:
{
lean_dec(v_h__3_1100_);
lean_dec(v_h__2_1099_);
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_h__4_1101_);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_apply_1(v_h__1_1098_, v___x_1102_);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; 
lean_dec(v_h__1_1098_);
v___x_1104_ = lean_apply_5(v_h__4_1101_, v_x_1096_, v_x_1097_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1104_;
}
}
case 1:
{
lean_dec(v_h__3_1100_);
lean_dec(v_h__1_1098_);
if (lean_obj_tag(v_x_1097_) == 1)
{
lean_object* v_pre_1105_; lean_object* v_str_1106_; lean_object* v_pre_1107_; lean_object* v_str_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__4_1101_);
v_pre_1105_ = lean_ctor_get(v_x_1096_, 0);
lean_inc(v_pre_1105_);
v_str_1106_ = lean_ctor_get(v_x_1096_, 1);
lean_inc_ref(v_str_1106_);
lean_dec_ref_known(v_x_1096_, 2);
v_pre_1107_ = lean_ctor_get(v_x_1097_, 0);
lean_inc(v_pre_1107_);
v_str_1108_ = lean_ctor_get(v_x_1097_, 1);
lean_inc_ref(v_str_1108_);
lean_dec_ref_known(v_x_1097_, 2);
v___x_1109_ = lean_apply_4(v_h__2_1099_, v_pre_1105_, v_str_1106_, v_pre_1107_, v_str_1108_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; 
lean_dec(v_h__2_1099_);
v___x_1110_ = lean_apply_5(v_h__4_1101_, v_x_1096_, v_x_1097_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1110_;
}
}
default: 
{
lean_dec(v_h__2_1099_);
lean_dec(v_h__1_1098_);
if (lean_obj_tag(v_x_1097_) == 2)
{
lean_object* v_pre_1111_; lean_object* v_i_1112_; lean_object* v_pre_1113_; lean_object* v_i_1114_; lean_object* v___x_1115_; 
lean_dec(v_h__4_1101_);
v_pre_1111_ = lean_ctor_get(v_x_1096_, 0);
lean_inc(v_pre_1111_);
v_i_1112_ = lean_ctor_get(v_x_1096_, 1);
lean_inc(v_i_1112_);
lean_dec_ref_known(v_x_1096_, 2);
v_pre_1113_ = lean_ctor_get(v_x_1097_, 0);
lean_inc(v_pre_1113_);
v_i_1114_ = lean_ctor_get(v_x_1097_, 1);
lean_inc(v_i_1114_);
lean_dec_ref_known(v_x_1097_, 2);
v___x_1115_ = lean_apply_4(v_h__3_1100_, v_pre_1111_, v_i_1112_, v_pre_1113_, v_i_1114_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
lean_dec(v_h__3_1100_);
v___x_1116_ = lean_apply_5(v_h__4_1101_, v_x_1096_, v_x_1097_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1117_, lean_object* v_b_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_name_eq(v_a_1117_, v_b_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1120_, lean_object* v_b_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Lean_Name_instDecidableEq(v_a_1120_, v_b_1121_);
lean_dec(v_b_1121_);
lean_dec(v_a_1120_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1124_){
_start:
{
lean_object* v_namePrefix_1125_; lean_object* v_idx_1126_; lean_object* v___x_1127_; 
v_namePrefix_1125_ = lean_ctor_get(v_g_1124_, 0);
lean_inc(v_namePrefix_1125_);
v_idx_1126_ = lean_ctor_get(v_g_1124_, 1);
lean_inc(v_idx_1126_);
lean_dec_ref(v_g_1124_);
v___x_1127_ = l_Lean_Name_num___override(v_namePrefix_1125_, v_idx_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1128_){
_start:
{
lean_object* v_namePrefix_1129_; lean_object* v_idx_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1139_; 
v_namePrefix_1129_ = lean_ctor_get(v_g_1128_, 0);
v_idx_1130_ = lean_ctor_get(v_g_1128_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_g_1128_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1132_ = v_g_1128_;
v_isShared_1133_ = v_isSharedCheck_1139_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_idx_1130_);
lean_inc(v_namePrefix_1129_);
lean_dec(v_g_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1139_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_nat_add(v_idx_1130_, v___x_1134_);
lean_dec(v_idx_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1135_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_namePrefix_1129_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1140_){
_start:
{
lean_object* v_namePrefix_1141_; lean_object* v_idx_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1154_; 
v_namePrefix_1141_ = lean_ctor_get(v_g_1140_, 0);
v_idx_1142_ = lean_ctor_get(v_g_1140_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_g_1140_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1144_ = v_g_1140_;
v_isShared_1145_ = v_isSharedCheck_1154_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_idx_1142_);
lean_inc(v_namePrefix_1141_);
lean_dec(v_g_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1154_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_inc(v_idx_1142_);
lean_inc(v_namePrefix_1141_);
v___x_1146_ = l_Lean_Name_num___override(v_namePrefix_1141_, v_idx_1142_);
v___x_1147_ = lean_unsigned_to_nat(1u);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1147_);
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1149_ = v___x_1144_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_nat_add(v_idx_1142_, v___x_1147_);
lean_dec(v_idx_1142_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_namePrefix_1141_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1149_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
return v___x_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1155_, lean_object* v_r_1156_, lean_object* v_____r_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_apply_2(v_toPure_1155_, lean_box(0), v_r_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1159_, lean_object* v_setNGen_1160_, lean_object* v_toBind_1161_, lean_object* v_ngen_1162_){
_start:
{
lean_object* v_namePrefix_1163_; lean_object* v_idx_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1177_; 
v_namePrefix_1163_ = lean_ctor_get(v_ngen_1162_, 0);
v_idx_1164_ = lean_ctor_get(v_ngen_1162_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_ngen_1162_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1166_ = v_ngen_1162_;
v_isShared_1167_ = v_isSharedCheck_1177_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_idx_1164_);
lean_inc(v_namePrefix_1163_);
lean_dec(v_ngen_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1177_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_r_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_inc(v_idx_1164_);
lean_inc(v_namePrefix_1163_);
v_r_1168_ = l_Lean_Name_num___override(v_namePrefix_1163_, v_idx_1164_);
v___f_1169_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1169_, 0, v_toPure_1159_);
lean_closure_set(v___f_1169_, 1, v_r_1168_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_idx_1164_, v___x_1170_);
lean_dec(v_idx_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1171_);
v___x_1173_ = v___x_1166_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_namePrefix_1163_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_apply_1(v_setNGen_1160_, v___x_1173_);
v___x_1175_ = lean_apply_4(v_toBind_1161_, lean_box(0), lean_box(0), v___x_1174_, v___f_1169_);
return v___x_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v_toApplicative_1180_; lean_object* v_toBind_1181_; lean_object* v_getNGen_1182_; lean_object* v_setNGen_1183_; lean_object* v_toPure_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_toApplicative_1180_ = lean_ctor_get(v_inst_1178_, 0);
lean_inc_ref(v_toApplicative_1180_);
v_toBind_1181_ = lean_ctor_get(v_inst_1178_, 1);
lean_inc_n(v_toBind_1181_, 2);
lean_dec_ref(v_inst_1178_);
v_getNGen_1182_ = lean_ctor_get(v_inst_1179_, 0);
lean_inc(v_getNGen_1182_);
v_setNGen_1183_ = lean_ctor_get(v_inst_1179_, 1);
lean_inc(v_setNGen_1183_);
lean_dec_ref(v_inst_1179_);
v_toPure_1184_ = lean_ctor_get(v_toApplicative_1180_, 1);
lean_inc(v_toPure_1184_);
lean_dec_ref(v_toApplicative_1180_);
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1185_, 0, v_toPure_1184_);
lean_closure_set(v___f_1185_, 1, v_setNGen_1183_);
lean_closure_set(v___f_1185_, 2, v_toBind_1181_);
v___x_1186_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v_getNGen_1182_, v___f_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_mkFreshId___redArg(v_inst_1188_, v_inst_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1191_, lean_object* v_inst_1192_, lean_object* v_ngen_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_apply_1(v_setNGen_1191_, v_ngen_1193_);
v___x_1195_ = lean_apply_2(v_inst_1192_, lean_box(0), v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v_getNGen_1198_; lean_object* v_setNGen_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_getNGen_1198_ = lean_ctor_get(v_inst_1197_, 0);
v_setNGen_1199_ = lean_ctor_get(v_inst_1197_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_inst_1197_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v_inst_1197_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_setNGen_1199_);
lean_inc(v_getNGen_1198_);
lean_dec(v_inst_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_inc(v_inst_1196_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1203_, 0, v_setNGen_1199_);
lean_closure_set(v___f_1203_, 1, v_inst_1196_);
v___x_1204_ = lean_apply_2(v_inst_1196_, lean_box(0), v_getNGen_1198_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___f_1203_);
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___f_1203_);
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
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1209_, lean_object* v_n_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1211_, v_inst_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
lean_dec(v_x_1214_);
return v_x_1215_;
}
else
{
lean_object* v_head_1217_; lean_object* v_tail_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
v_head_1217_ = lean_ctor_get(v_x_1216_, 0);
v_tail_1218_ = lean_ctor_get(v_x_1216_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x_1216_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1220_ = v_x_1216_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_tail_1218_);
lean_inc(v_head_1217_);
lean_dec(v_x_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
lean_inc(v_x_1214_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 5);
lean_ctor_set(v___x_1220_, 1, v_x_1214_);
lean_ctor_set(v___x_1220_, 0, v_x_1215_);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_x_1215_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_x_1214_);
v___x_1223_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = l_String_quote(v_head_1217_);
v___x_1225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1223_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v_x_1215_ = v___x_1226_;
v_x_1216_ = v_tail_1218_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_dec(v_x_1230_);
return v_x_1231_;
}
else
{
lean_object* v_head_1233_; lean_object* v_tail_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1245_; 
v_head_1233_ = lean_ctor_get(v_x_1232_, 0);
v_tail_1234_ = lean_ctor_get(v_x_1232_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1232_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1236_ = v_x_1232_;
v_isShared_1237_ = v_isSharedCheck_1245_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_tail_1234_);
lean_inc(v_head_1233_);
lean_dec(v_x_1232_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1245_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
lean_inc(v_x_1230_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set_tag(v___x_1236_, 5);
lean_ctor_set(v___x_1236_, 1, v_x_1230_);
lean_ctor_set(v___x_1236_, 0, v_x_1231_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_x_1231_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_x_1230_);
v___x_1239_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1240_ = l_String_quote(v_head_1233_);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1239_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1230_, v___x_1242_, v_tail_1234_);
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = l_String_quote(v___y_1246_);
v___x_1248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
lean_object* v___x_1251_; 
lean_dec(v_x_1250_);
v___x_1251_ = lean_box(0);
return v___x_1251_;
}
else
{
lean_object* v_tail_1252_; 
v_tail_1252_ = lean_ctor_get(v_x_1249_, 1);
if (lean_obj_tag(v_tail_1252_) == 0)
{
lean_object* v_head_1253_; lean_object* v___x_1254_; 
lean_dec(v_x_1250_);
v_head_1253_ = lean_ctor_get(v_x_1249_, 0);
lean_inc(v_head_1253_);
lean_dec_ref_known(v_x_1249_, 2);
v___x_1254_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1253_);
return v___x_1254_;
}
else
{
lean_object* v_head_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc(v_tail_1252_);
v_head_1255_ = lean_ctor_get(v_x_1249_, 0);
lean_inc(v_head_1255_);
lean_dec_ref_known(v_x_1249_, 2);
v___x_1256_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1255_);
v___x_1257_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1250_, v___x_1256_, v_tail_1252_);
return v___x_1257_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1270_ = lean_string_length(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1272_ = lean_nat_to_int(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1277_){
_start:
{
if (lean_obj_tag(v_a_1277_) == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1279_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1280_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1277_, v___x_1279_);
v___x_1281_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1282_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1280_);
v___x_1284_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1281_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Std_Format_fill(v___x_1286_);
return v___x_1287_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(2u);
v___x_1295_ = lean_nat_to_int(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_to_int(v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1304_, lean_object* v_prec_1305_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_ns_1306_; lean_object* v___y_1308_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_ns_1306_ = lean_ctor_get(v_x_1304_, 0);
lean_inc(v_ns_1306_);
lean_dec_ref_known(v_x_1304_, 1);
v___x_1317_ = lean_unsigned_to_nat(1024u);
v___x_1318_ = lean_nat_dec_le(v___x_1317_, v_prec_1305_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1308_ = v___x_1319_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1308_ = v___x_1320_;
goto v___jp_1307_;
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1309_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1310_ = lean_unsigned_to_nat(1024u);
v___x_1311_ = l_Lean_Name_reprPrec(v_ns_1306_, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1309_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_inc(v___y_1308_);
v___x_1313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___y_1308_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = 0;
v___x_1315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*1, v___x_1314_);
v___x_1316_ = l_Repr_addAppParen(v___x_1315_, v_prec_1305_);
return v___x_1316_;
}
}
else
{
lean_object* v_n_1321_; lean_object* v_fields_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1346_; 
v_n_1321_ = lean_ctor_get(v_x_1304_, 0);
v_fields_1322_ = lean_ctor_get(v_x_1304_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1324_ = v_x_1304_;
v_isShared_1325_ = v_isSharedCheck_1346_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_fields_1322_);
lean_inc(v_n_1321_);
lean_dec(v_x_1304_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1346_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___y_1327_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_unsigned_to_nat(1024u);
v___x_1343_ = lean_nat_dec_le(v___x_1342_, v_prec_1305_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1327_ = v___x_1344_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1327_ = v___x_1345_;
goto v___jp_1326_;
}
v___jp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1328_ = lean_box(1);
v___x_1329_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1330_ = lean_unsigned_to_nat(1024u);
v___x_1331_ = l_Lean_Name_reprPrec(v_n_1321_, v___x_1330_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set_tag(v___x_1324_, 5);
lean_ctor_set(v___x_1324_, 1, v___x_1331_);
lean_ctor_set(v___x_1324_, 0, v___x_1329_);
v___x_1333_ = v___x_1324_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1328_);
v___x_1335_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1322_);
v___x_1336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
lean_inc(v___y_1327_);
v___x_1337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___y_1327_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = 0;
v___x_1339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*1, v___x_1338_);
v___x_1340_ = l_Repr_addAppParen(v___x_1339_, v_prec_1305_);
return v___x_1340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1347_, lean_object* v_prec_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1347_, v_prec_1348_);
lean_dec(v_prec_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_nat_to_int(v_a_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1352_, lean_object* v_n_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1355_, lean_object* v_n_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1355_, v_n_1356_);
lean_dec(v_n_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1360_, v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1365_) == 0)
{
lean_dec(v_x_1363_);
return v_x_1364_;
}
else
{
lean_object* v_head_1366_; lean_object* v_tail_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1378_; 
v_head_1366_ = lean_ctor_get(v_x_1365_, 0);
v_tail_1367_ = lean_ctor_get(v_x_1365_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1365_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1369_ = v_x_1365_;
v_isShared_1370_ = v_isSharedCheck_1378_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_tail_1367_);
lean_inc(v_head_1366_);
lean_dec(v_x_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1378_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
lean_inc(v_x_1363_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 5);
lean_ctor_set(v___x_1369_, 1, v_x_1363_);
lean_ctor_set(v___x_1369_, 0, v_x_1364_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_x_1364_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_x_1363_);
v___x_1372_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1366_, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1372_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v_x_1364_ = v___x_1375_;
v_x_1365_ = v_tail_1367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_dec(v_x_1379_);
return v_x_1380_;
}
else
{
lean_object* v_head_1382_; lean_object* v_tail_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1394_; 
v_head_1382_ = lean_ctor_get(v_x_1381_, 0);
v_tail_1383_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1385_ = v_x_1381_;
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_tail_1383_);
lean_inc(v_head_1382_);
lean_dec(v_x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
lean_inc(v_x_1379_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 5);
lean_ctor_set(v___x_1385_, 1, v_x_1379_);
lean_ctor_set(v___x_1385_, 0, v_x_1380_);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_x_1380_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_x_1379_);
v___x_1388_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1382_, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1388_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1379_, v___x_1391_, v_tail_1383_);
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_x_1396_);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
else
{
lean_object* v_tail_1398_; 
v_tail_1398_ = lean_ctor_get(v_x_1395_, 1);
if (lean_obj_tag(v_tail_1398_) == 0)
{
lean_object* v_head_1399_; lean_object* v___x_1400_; 
lean_dec(v_x_1396_);
v_head_1399_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_head_1399_);
lean_dec_ref_known(v_x_1395_, 2);
v___x_1400_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1399_);
return v___x_1400_;
}
else
{
lean_object* v_head_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc(v_tail_1398_);
v_head_1401_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_head_1401_);
lean_dec_ref_known(v_x_1395_, 2);
v___x_1402_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1401_);
v___x_1403_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1396_, v___x_1402_, v_tail_1398_);
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1404_){
_start:
{
if (lean_obj_tag(v_a_1404_) == 0)
{
lean_object* v___x_1405_; 
v___x_1405_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1406_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1407_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1404_, v___x_1406_);
v___x_1408_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1409_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___x_1407_);
v___x_1411_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1408_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = 0;
v___x_1415_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*1, v___x_1414_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_dec(v_x_1425_);
return v_x_1426_;
}
else
{
lean_object* v_head_1428_; lean_object* v_tail_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1440_; 
v_head_1428_ = lean_ctor_get(v_x_1427_, 0);
v_tail_1429_ = lean_ctor_get(v_x_1427_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1427_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1431_ = v_x_1427_;
v_isShared_1432_ = v_isSharedCheck_1440_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_tail_1429_);
lean_inc(v_head_1428_);
lean_dec(v_x_1427_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1440_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
lean_inc(v_x_1425_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 5);
lean_ctor_set(v___x_1431_, 1, v_x_1425_);
lean_ctor_set(v___x_1431_, 0, v_x_1426_);
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_x_1426_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_x_1425_);
v___x_1434_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = l_Lean_Syntax_instRepr_repr(v_head_1428_, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1434_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v_x_1426_ = v___x_1437_;
v_x_1427_ = v_tail_1429_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
if (lean_obj_tag(v_x_1443_) == 0)
{
lean_dec(v_x_1441_);
return v_x_1442_;
}
else
{
lean_object* v_head_1444_; lean_object* v_tail_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1456_; 
v_head_1444_ = lean_ctor_get(v_x_1443_, 0);
v_tail_1445_ = lean_ctor_get(v_x_1443_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1443_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1447_ = v_x_1443_;
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_tail_1445_);
lean_inc(v_head_1444_);
lean_dec(v_x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
lean_inc(v_x_1441_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 5);
lean_ctor_set(v___x_1447_, 1, v_x_1441_);
lean_ctor_set(v___x_1447_, 0, v_x_1442_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_x_1442_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_x_1441_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = l_Lean_Syntax_instRepr_repr(v_head_1444_, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1450_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1441_, v___x_1453_, v_tail_1445_);
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
if (lean_obj_tag(v_x_1457_) == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_x_1458_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
lean_object* v_tail_1460_; 
v_tail_1460_ = lean_ctor_get(v_x_1457_, 1);
if (lean_obj_tag(v_tail_1460_) == 0)
{
lean_object* v_head_1461_; lean_object* v___x_1462_; 
lean_dec(v_x_1458_);
v_head_1461_ = lean_ctor_get(v_x_1457_, 0);
lean_inc(v_head_1461_);
lean_dec_ref_known(v_x_1457_, 2);
v___x_1462_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1461_);
return v___x_1462_;
}
else
{
lean_object* v_head_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc(v_tail_1460_);
v_head_1463_ = lean_ctor_get(v_x_1457_, 0);
lean_inc(v_head_1463_);
lean_dec_ref_known(v_x_1457_, 2);
v___x_1464_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1463_);
v___x_1465_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1458_, v___x_1464_, v_tail_1460_);
return v___x_1465_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1468_ = lean_string_length(v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1470_ = lean_nat_to_int(v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_array_get_size(v_xs_1476_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_nat_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1480_ = lean_array_to_list(v_xs_1476_);
v___x_1481_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1482_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1480_, v___x_1481_);
v___x_1483_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1484_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1482_);
v___x_1486_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1483_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Std_Format_fill(v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
lean_dec_ref(v_xs_1476_);
v___x_1490_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1504_, lean_object* v_prec_1505_){
_start:
{
lean_object* v___y_1507_; 
switch(lean_obj_tag(v_x_1504_))
{
case 0:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = lean_unsigned_to_nat(1024u);
v___x_1514_ = lean_nat_dec_le(v___x_1513_, v_prec_1505_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1507_ = v___x_1515_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1507_ = v___x_1516_;
goto v___jp_1506_;
}
}
case 1:
{
lean_object* v_info_1517_; lean_object* v_kind_1518_; lean_object* v_args_1519_; lean_object* v___y_1521_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_info_1517_ = lean_ctor_get(v_x_1504_, 0);
lean_inc(v_info_1517_);
v_kind_1518_ = lean_ctor_get(v_x_1504_, 1);
lean_inc(v_kind_1518_);
v_args_1519_ = lean_ctor_get(v_x_1504_, 2);
lean_inc_ref(v_args_1519_);
lean_dec_ref_known(v_x_1504_, 3);
v___x_1537_ = lean_unsigned_to_nat(1024u);
v___x_1538_ = lean_nat_dec_le(v___x_1537_, v_prec_1505_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1521_ = v___x_1539_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1521_ = v___x_1540_;
goto v___jp_1520_;
}
v___jp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1522_ = lean_box(1);
v___x_1523_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1524_ = lean_unsigned_to_nat(1024u);
v___x_1525_ = l_instReprSourceInfo_repr(v_info_1517_, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1523_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1522_);
v___x_1528_ = l_Lean_Name_reprPrec(v_kind_1518_, v___x_1524_);
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1522_);
v___x_1531_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1519_);
v___x_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
lean_inc(v___y_1521_);
v___x_1533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___y_1521_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = 0;
v___x_1535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*1, v___x_1534_);
v___x_1536_ = l_Repr_addAppParen(v___x_1535_, v_prec_1505_);
return v___x_1536_;
}
}
case 2:
{
lean_object* v_info_1541_; lean_object* v_val_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1567_; 
v_info_1541_ = lean_ctor_get(v_x_1504_, 0);
v_val_1542_ = lean_ctor_get(v_x_1504_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1504_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1544_ = v_x_1504_;
v_isShared_1545_ = v_isSharedCheck_1567_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_val_1542_);
lean_inc(v_info_1541_);
lean_dec(v_x_1504_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1567_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___y_1547_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = lean_unsigned_to_nat(1024u);
v___x_1564_ = lean_nat_dec_le(v___x_1563_, v_prec_1505_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1547_ = v___x_1565_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1547_ = v___x_1566_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1548_ = lean_box(1);
v___x_1549_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1550_ = lean_unsigned_to_nat(1024u);
v___x_1551_ = l_instReprSourceInfo_repr(v_info_1541_, v___x_1550_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 5);
lean_ctor_set(v___x_1544_, 1, v___x_1551_);
lean_ctor_set(v___x_1544_, 0, v___x_1549_);
v___x_1553_ = v___x_1544_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1548_);
v___x_1555_ = l_String_quote(v_val_1542_);
v___x_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1554_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
lean_inc(v___y_1547_);
v___x_1558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___y_1547_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = 0;
v___x_1560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*1, v___x_1559_);
v___x_1561_ = l_Repr_addAppParen(v___x_1560_, v_prec_1505_);
return v___x_1561_;
}
}
}
}
default: 
{
lean_object* v_info_1568_; lean_object* v_rawVal_1569_; lean_object* v_val_1570_; lean_object* v_preresolved_1571_; lean_object* v___y_1573_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_info_1568_ = lean_ctor_get(v_x_1504_, 0);
lean_inc(v_info_1568_);
v_rawVal_1569_ = lean_ctor_get(v_x_1504_, 1);
lean_inc_ref(v_rawVal_1569_);
v_val_1570_ = lean_ctor_get(v_x_1504_, 2);
lean_inc(v_val_1570_);
v_preresolved_1571_ = lean_ctor_get(v_x_1504_, 3);
lean_inc(v_preresolved_1571_);
lean_dec_ref_known(v_x_1504_, 4);
v___x_1596_ = lean_unsigned_to_nat(1024u);
v___x_1597_ = lean_nat_dec_le(v___x_1596_, v_prec_1505_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1573_ = v___x_1598_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1573_ = v___x_1599_;
goto v___jp_1572_;
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1574_ = lean_box(1);
v___x_1575_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1576_ = lean_unsigned_to_nat(1024u);
v___x_1577_ = l_instReprSourceInfo_repr(v_info_1568_, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1575_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___x_1574_);
v___x_1580_ = lean_substring_tostring(v_rawVal_1569_);
v___x_1581_ = l_String_quote(v___x_1580_);
v___x_1582_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1583_ = lean_string_append(v___x_1581_, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1579_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v___x_1574_);
v___x_1587_ = l_Lean_Name_reprPrec(v_val_1570_, v___x_1576_);
v___x_1588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1574_);
v___x_1590_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1571_);
v___x_1591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
lean_inc(v___y_1573_);
v___x_1592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___y_1573_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = 0;
v___x_1594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set_uint8(v___x_1594_, sizeof(void*)*1, v___x_1593_);
v___x_1595_ = l_Repr_addAppParen(v___x_1594_, v_prec_1505_);
return v___x_1595_;
}
}
}
v___jp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1508_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1507_);
v___x_1509_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___y_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = 0;
v___x_1511_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*1, v___x_1510_);
v___x_1512_ = l_Repr_addAppParen(v___x_1511_, v_prec_1505_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = l_Lean_Syntax_instRepr_repr(v___y_1600_, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1603_, lean_object* v_prec_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Syntax_instRepr_repr(v_x_1603_, v_prec_1604_);
lean_dec(v_prec_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1606_, lean_object* v_n_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1609_, lean_object* v_n_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1609_, v_n_1610_);
lean_dec(v_n_1610_);
return v_res_1611_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_unsigned_to_nat(7u);
v___x_1628_ = lean_nat_to_int(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1631_ = lean_string_length(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1633_ = lean_nat_to_int(v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1639_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1640_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = l_Lean_Syntax_instRepr_repr(v_x_1638_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1640_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = 0;
v___x_1645_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1639_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1648_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1646_);
v___x_1650_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1647_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*1, v___x_1644_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1654_, lean_object* v_x_1655_, lean_object* v_prec_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1658_, lean_object* v_x_1659_, lean_object* v_prec_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1658_, v_x_1659_, v_prec_1660_);
lean_dec(v_prec_1660_);
lean_dec(v_ks_1658_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1663_, 0, v_ks_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1664_){
_start:
{
lean_inc(v_stx_1664_);
return v_stx_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1665_);
lean_dec(v_stx_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1669_; 
v___f_1669_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1672_, lean_object* v_ks_1673_){
_start:
{
lean_object* v___f_1674_; 
v___f_1674_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1675_, lean_object* v_ks_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1675_, v_ks_1676_);
lean_dec(v_ks_1676_);
lean_dec(v_k_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1679_; 
v___f_1679_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1682_, lean_object* v_k_x27_1683_){
_start:
{
lean_object* v___f_1684_; 
v___f_1684_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1685_, lean_object* v_k_x27_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1685_, v_k_x27_1686_);
lean_dec(v_k_x27_1686_);
lean_dec(v_ks_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1688_){
_start:
{
lean_inc(v_s_1688_);
return v_s_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1689_);
lean_dec(v_s_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1693_, lean_object* v_ss_1694_, lean_object* v_n_1695_, lean_object* v_res_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1697_, 0, v_info_1693_);
lean_ctor_set(v___x_1697_, 1, v_ss_1694_);
lean_ctor_set(v___x_1697_, 2, v_n_1695_);
lean_ctor_set(v___x_1697_, 3, v_res_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1707_; 
v___f_1707_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1710_){
_start:
{
lean_object* v___f_1711_; 
v___f_1711_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1712_);
lean_dec(v_k_1712_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1715_, 0, v_k_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
if (lean_obj_tag(v_x_1717_) == 0)
{
uint8_t v___x_1718_; 
v___x_1718_ = 1;
return v___x_1718_;
}
else
{
uint8_t v___x_1719_; 
v___x_1719_ = 0;
return v___x_1719_;
}
}
else
{
if (lean_obj_tag(v_x_1717_) == 0)
{
uint8_t v___x_1720_; 
v___x_1720_ = 0;
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v_head_1723_; lean_object* v_tail_1724_; uint8_t v___x_1725_; 
v_head_1721_ = lean_ctor_get(v_x_1716_, 0);
v_tail_1722_ = lean_ctor_get(v_x_1716_, 1);
v_head_1723_ = lean_ctor_get(v_x_1717_, 0);
v_tail_1724_ = lean_ctor_get(v_x_1717_, 1);
v___x_1725_ = lean_string_dec_eq(v_head_1721_, v_head_1723_);
if (v___x_1725_ == 0)
{
return v___x_1725_;
}
else
{
v_x_1716_ = v_tail_1722_;
v_x_1717_ = v_tail_1724_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
uint8_t v_res_1729_; lean_object* v_r_1730_; 
v_res_1729_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1727_, v_x_1728_);
lean_dec(v_x_1728_);
lean_dec(v_x_1727_);
v_r_1730_ = lean_box(v_res_1729_);
return v_r_1730_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
if (lean_obj_tag(v_x_1731_) == 0)
{
if (lean_obj_tag(v_x_1732_) == 0)
{
lean_object* v_ns_1733_; lean_object* v_ns_1734_; uint8_t v___x_1735_; 
v_ns_1733_ = lean_ctor_get(v_x_1731_, 0);
v_ns_1734_ = lean_ctor_get(v_x_1732_, 0);
v___x_1735_ = lean_name_eq(v_ns_1733_, v_ns_1734_);
return v___x_1735_;
}
else
{
uint8_t v___x_1736_; 
v___x_1736_ = 0;
return v___x_1736_;
}
}
else
{
if (lean_obj_tag(v_x_1732_) == 1)
{
lean_object* v_n_1737_; lean_object* v_fields_1738_; lean_object* v_n_1739_; lean_object* v_fields_1740_; uint8_t v___x_1741_; 
v_n_1737_ = lean_ctor_get(v_x_1731_, 0);
v_fields_1738_ = lean_ctor_get(v_x_1731_, 1);
v_n_1739_ = lean_ctor_get(v_x_1732_, 0);
v_fields_1740_ = lean_ctor_get(v_x_1732_, 1);
v___x_1741_ = lean_name_eq(v_n_1737_, v_n_1739_);
if (v___x_1741_ == 0)
{
return v___x_1741_;
}
else
{
uint8_t v___x_1742_; 
v___x_1742_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1738_, v_fields_1740_);
return v___x_1742_;
}
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = 0;
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1744_, v_x_1745_);
lean_dec_ref(v_x_1745_);
lean_dec_ref(v_x_1744_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
if (lean_obj_tag(v_x_1751_) == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = 1;
return v___x_1752_;
}
else
{
uint8_t v___x_1753_; 
v___x_1753_ = 0;
return v___x_1753_;
}
}
else
{
if (lean_obj_tag(v_x_1751_) == 0)
{
uint8_t v___x_1754_; 
v___x_1754_ = 0;
return v___x_1754_;
}
else
{
lean_object* v_head_1755_; lean_object* v_tail_1756_; lean_object* v_head_1757_; lean_object* v_tail_1758_; uint8_t v___x_1759_; 
v_head_1755_ = lean_ctor_get(v_x_1750_, 0);
v_tail_1756_ = lean_ctor_get(v_x_1750_, 1);
v_head_1757_ = lean_ctor_get(v_x_1751_, 0);
v_tail_1758_ = lean_ctor_get(v_x_1751_, 1);
v___x_1759_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1755_, v_head_1757_);
if (v___x_1759_ == 0)
{
return v___x_1759_;
}
else
{
v_x_1750_ = v_tail_1756_;
v_x_1751_ = v_tail_1758_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1761_, lean_object* v_x_1762_){
_start:
{
uint8_t v_res_1763_; lean_object* v_r_1764_; 
v_res_1763_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1761_, v_x_1762_);
lean_dec(v_x_1762_);
lean_dec(v_x_1761_);
v_r_1764_ = lean_box(v_res_1763_);
return v_r_1764_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
switch(lean_obj_tag(v_x_1765_))
{
case 0:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
uint8_t v___x_1767_; 
v___x_1767_ = 1;
return v___x_1767_;
}
else
{
uint8_t v___x_1768_; 
v___x_1768_ = 0;
return v___x_1768_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1766_) == 1)
{
lean_object* v_kind_1769_; lean_object* v_args_1770_; lean_object* v_kind_1771_; lean_object* v_args_1772_; uint8_t v___x_1773_; 
v_kind_1769_ = lean_ctor_get(v_x_1765_, 1);
v_args_1770_ = lean_ctor_get(v_x_1765_, 2);
v_kind_1771_ = lean_ctor_get(v_x_1766_, 1);
v_args_1772_ = lean_ctor_get(v_x_1766_, 2);
v___x_1773_ = lean_name_eq(v_kind_1769_, v_kind_1771_);
if (v___x_1773_ == 0)
{
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_array_get_size(v_args_1770_);
v___x_1775_ = lean_array_get_size(v_args_1772_);
v___x_1776_ = lean_nat_dec_eq(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
return v___x_1776_;
}
else
{
uint8_t v___x_1777_; 
v___x_1777_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1770_, v_args_1772_, v___x_1774_);
return v___x_1777_;
}
}
}
else
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1766_) == 2)
{
lean_object* v_val_1779_; lean_object* v_val_1780_; uint8_t v___x_1781_; 
v_val_1779_ = lean_ctor_get(v_x_1765_, 1);
v_val_1780_ = lean_ctor_get(v_x_1766_, 1);
v___x_1781_ = lean_string_dec_eq(v_val_1779_, v_val_1780_);
return v___x_1781_;
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = 0;
return v___x_1782_;
}
}
default: 
{
if (lean_obj_tag(v_x_1766_) == 3)
{
lean_object* v_rawVal_1783_; lean_object* v_val_1784_; lean_object* v_preresolved_1785_; lean_object* v_rawVal_1786_; lean_object* v_val_1787_; lean_object* v_preresolved_1788_; uint8_t v___y_1790_; uint8_t v___x_1792_; 
v_rawVal_1783_ = lean_ctor_get(v_x_1765_, 1);
v_val_1784_ = lean_ctor_get(v_x_1765_, 2);
v_preresolved_1785_ = lean_ctor_get(v_x_1765_, 3);
v_rawVal_1786_ = lean_ctor_get(v_x_1766_, 1);
v_val_1787_ = lean_ctor_get(v_x_1766_, 2);
v_preresolved_1788_ = lean_ctor_get(v_x_1766_, 3);
lean_inc_ref(v_rawVal_1786_);
lean_inc_ref(v_rawVal_1783_);
v___x_1792_ = lean_substring_beq(v_rawVal_1783_, v_rawVal_1786_);
if (v___x_1792_ == 0)
{
v___y_1790_ = v___x_1792_;
goto v___jp_1789_;
}
else
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_name_eq(v_val_1784_, v_val_1787_);
v___y_1790_ = v___x_1793_;
goto v___jp_1789_;
}
v___jp_1789_:
{
if (v___y_1790_ == 0)
{
return v___y_1790_;
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1785_, v_preresolved_1788_);
return v___x_1791_;
}
}
}
else
{
uint8_t v___x_1794_; 
v___x_1794_ = 0;
return v___x_1794_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1795_, lean_object* v_ys_1796_, lean_object* v_x_1797_){
_start:
{
lean_object* v_zero_1798_; uint8_t v_isZero_1799_; 
v_zero_1798_ = lean_unsigned_to_nat(0u);
v_isZero_1799_ = lean_nat_dec_eq(v_x_1797_, v_zero_1798_);
if (v_isZero_1799_ == 1)
{
lean_dec(v_x_1797_);
return v_isZero_1799_;
}
else
{
lean_object* v_one_1800_; lean_object* v_n_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_one_1800_ = lean_unsigned_to_nat(1u);
v_n_1801_ = lean_nat_sub(v_x_1797_, v_one_1800_);
lean_dec(v_x_1797_);
v___x_1802_ = lean_array_fget_borrowed(v_xs_1795_, v_n_1801_);
v___x_1803_ = lean_array_fget_borrowed(v_ys_1796_, v_n_1801_);
v___x_1804_ = l_Lean_Syntax_structEq(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec(v_n_1801_);
return v___x_1804_;
}
else
{
v_x_1797_ = v_n_1801_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1806_, lean_object* v_ys_1807_, lean_object* v_x_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1806_, v_ys_1807_, v_x_1808_);
lean_dec_ref(v_ys_1807_);
lean_dec_ref(v_xs_1806_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l_Lean_Syntax_structEq(v_x_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec(v_x_1811_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1815_, lean_object* v_ys_1816_, lean_object* v_hsz_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1815_, v_ys_1816_, v_x_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1821_, lean_object* v_ys_1822_, lean_object* v_hsz_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1821_, v_ys_1822_, v_hsz_1823_, v_x_1824_, v_x_1825_);
lean_dec_ref(v_ys_1822_);
lean_dec_ref(v_xs_1821_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1832_; 
v___f_1832_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1835_){
_start:
{
lean_object* v___f_1836_; 
v___f_1836_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Syntax_instBEqTSyntax(v_k_1837_);
lean_dec(v_k_1837_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1839_, lean_object* v_i_1840_){
_start:
{
lean_object* v_zero_1841_; uint8_t v_isZero_1842_; 
v_zero_1841_ = lean_unsigned_to_nat(0u);
v_isZero_1842_ = lean_nat_dec_eq(v_i_1840_, v_zero_1841_);
if (v_isZero_1842_ == 1)
{
lean_object* v___x_1843_; 
lean_dec(v_i_1840_);
v___x_1843_ = lean_box(0);
return v___x_1843_;
}
else
{
lean_object* v_one_1844_; lean_object* v_n_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_one_1844_ = lean_unsigned_to_nat(1u);
v_n_1845_ = lean_nat_sub(v_i_1840_, v_one_1844_);
lean_dec(v_i_1840_);
v___x_1846_ = lean_array_fget_borrowed(v_as_1839_, v_n_1845_);
v___x_1847_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1846_);
if (lean_obj_tag(v___x_1847_) == 0)
{
v_i_1840_ = v_n_1845_;
goto _start;
}
else
{
lean_dec(v_n_1845_);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1849_){
_start:
{
switch(lean_obj_tag(v_x_1849_))
{
case 2:
{
lean_object* v_info_1850_; lean_object* v___x_1851_; 
v_info_1850_ = lean_ctor_get(v_x_1849_, 0);
lean_inc(v_info_1850_);
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_info_1850_);
return v___x_1851_;
}
case 3:
{
lean_object* v_info_1852_; lean_object* v___x_1853_; 
v_info_1852_ = lean_ctor_get(v_x_1849_, 0);
lean_inc(v_info_1852_);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_info_1852_);
return v___x_1853_;
}
case 1:
{
lean_object* v_info_1854_; 
v_info_1854_ = lean_ctor_get(v_x_1849_, 0);
if (lean_obj_tag(v_info_1854_) == 2)
{
lean_object* v_args_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_args_1855_ = lean_ctor_get(v_x_1849_, 2);
v___x_1856_ = lean_array_get_size(v_args_1855_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1855_, v___x_1856_);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; 
lean_inc(v_info_1854_);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_info_1854_);
return v___x_1858_;
}
}
default: 
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1860_);
lean_dec(v_x_1860_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1862_, lean_object* v_i_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1862_, v_i_1863_);
lean_dec_ref(v_as_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1865_, lean_object* v_i_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1865_, v_i_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1869_, lean_object* v_i_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1869_, v_i_1870_, v_a_1871_);
lean_dec_ref(v_as_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1873_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_box(2);
return v___x_1875_;
}
else
{
lean_object* v_val_1876_; 
v_val_1876_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1876_);
lean_dec_ref_known(v___x_1874_, 1);
return v_val_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Syntax_getTailInfo(v_stx_1877_);
lean_dec(v_stx_1877_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1879_);
if (lean_obj_tag(v___x_1880_) == 1)
{
lean_object* v_val_1881_; 
v_val_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v___x_1880_, 1);
if (lean_obj_tag(v_val_1881_) == 0)
{
lean_object* v_trailing_1882_; lean_object* v_startPos_1883_; lean_object* v_stopPos_1884_; lean_object* v___x_1885_; 
v_trailing_1882_ = lean_ctor_get(v_val_1881_, 2);
lean_inc_ref(v_trailing_1882_);
lean_dec_ref_known(v_val_1881_, 4);
v_startPos_1883_ = lean_ctor_get(v_trailing_1882_, 1);
lean_inc(v_startPos_1883_);
v_stopPos_1884_ = lean_ctor_get(v_trailing_1882_, 2);
lean_inc(v_stopPos_1884_);
lean_dec_ref(v_trailing_1882_);
v___x_1885_ = lean_nat_sub(v_stopPos_1884_, v_startPos_1883_);
lean_dec(v_startPos_1883_);
lean_dec(v_stopPos_1884_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; 
lean_dec(v_val_1881_);
v___x_1886_ = lean_unsigned_to_nat(0u);
return v___x_1886_;
}
}
else
{
lean_object* v___x_1887_; 
lean_dec(v___x_1880_);
v___x_1887_ = lean_unsigned_to_nat(0u);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Syntax_getTrailingSize(v_stx_1888_);
lean_dec(v_stx_1888_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = l_Lean_Syntax_getTailInfo(v_stx_1890_);
v___x_1892_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1891_);
lean_dec(v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1893_);
lean_dec(v_stx_1893_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1895_, uint8_t v_canonicalOnly_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = l_Lean_Syntax_getTailInfo(v_stx_1895_);
v___x_1898_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1897_, v_canonicalOnly_1896_);
lean_dec(v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1899_, lean_object* v_canonicalOnly_1900_){
_start:
{
uint8_t v_canonicalOnly_boxed_1901_; lean_object* v_res_1902_; 
v_canonicalOnly_boxed_1901_ = lean_unbox(v_canonicalOnly_1900_);
v_res_1902_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1899_, v_canonicalOnly_boxed_1901_);
lean_dec(v_stx_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1903_, uint8_t v_withLeading_1904_, uint8_t v_withTrailing_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Syntax_getHeadInfo(v_stx_1903_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_leading_1907_; lean_object* v_pos_1908_; lean_object* v___x_1909_; 
v_leading_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_ref(v_leading_1907_);
v_pos_1908_ = lean_ctor_get(v___x_1906_, 1);
lean_inc(v_pos_1908_);
lean_dec_ref_known(v___x_1906_, 4);
v___x_1909_ = l_Lean_Syntax_getTailInfo(v_stx_1903_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_trailing_1910_; lean_object* v_endPos_1911_; lean_object* v_str_1912_; lean_object* v_startPos_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1927_; 
v_trailing_1910_ = lean_ctor_get(v___x_1909_, 2);
lean_inc_ref(v_trailing_1910_);
v_endPos_1911_ = lean_ctor_get(v___x_1909_, 3);
lean_inc(v_endPos_1911_);
lean_dec_ref_known(v___x_1909_, 4);
v_str_1912_ = lean_ctor_get(v_leading_1907_, 0);
v_startPos_1913_ = lean_ctor_get(v_leading_1907_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_leading_1907_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_leading_1907_, 2);
lean_dec(v_unused_1928_);
v___x_1915_ = v_leading_1907_;
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_startPos_1913_);
lean_inc(v_str_1912_);
lean_dec(v_leading_1907_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1925_; 
if (v_withLeading_1904_ == 0)
{
lean_dec(v_startPos_1913_);
v___y_1925_ = v_pos_1908_;
goto v___jp_1924_;
}
else
{
lean_dec(v_pos_1908_);
v___y_1925_ = v_startPos_1913_;
goto v___jp_1924_;
}
v___jp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 2, v___y_1919_);
lean_ctor_set(v___x_1915_, 1, v___y_1918_);
v___x_1921_ = v___x_1915_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_str_1912_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___y_1918_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v___y_1919_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
v___jp_1924_:
{
if (v_withTrailing_1905_ == 0)
{
lean_dec_ref(v_trailing_1910_);
v___y_1918_ = v___y_1925_;
v___y_1919_ = v_endPos_1911_;
goto v___jp_1917_;
}
else
{
lean_object* v_stopPos_1926_; 
lean_dec(v_endPos_1911_);
v_stopPos_1926_ = lean_ctor_get(v_trailing_1910_, 2);
lean_inc(v_stopPos_1926_);
lean_dec_ref(v_trailing_1910_);
v___y_1918_ = v___y_1925_;
v___y_1919_ = v_stopPos_1926_;
goto v___jp_1917_;
}
}
}
}
else
{
lean_object* v___x_1929_; 
lean_dec(v___x_1909_);
lean_dec(v_pos_1908_);
lean_dec_ref(v_leading_1907_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
}
else
{
lean_object* v___x_1930_; 
lean_dec(v___x_1906_);
v___x_1930_ = lean_box(0);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1931_, lean_object* v_withLeading_1932_, lean_object* v_withTrailing_1933_){
_start:
{
uint8_t v_withLeading_boxed_1934_; uint8_t v_withTrailing_boxed_1935_; lean_object* v_res_1936_; 
v_withLeading_boxed_1934_ = lean_unbox(v_withLeading_1932_);
v_withTrailing_boxed_1935_ = lean_unbox(v_withTrailing_1933_);
v_res_1936_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1931_, v_withLeading_boxed_1934_, v_withTrailing_boxed_1935_);
lean_dec(v_stx_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1937_, lean_object* v_f_1938_, lean_object* v_i_1939_){
_start:
{
lean_object* v_zero_1940_; uint8_t v_isZero_1941_; 
v_zero_1940_ = lean_unsigned_to_nat(0u);
v_isZero_1941_ = lean_nat_dec_eq(v_i_1939_, v_zero_1940_);
if (v_isZero_1941_ == 1)
{
lean_object* v___x_1942_; 
lean_dec(v_i_1939_);
lean_dec_ref(v_f_1938_);
lean_dec_ref(v_a_1937_);
v___x_1942_ = lean_box(0);
return v___x_1942_;
}
else
{
lean_object* v_one_1943_; lean_object* v_n_1944_; lean_object* v_v_1945_; lean_object* v___x_1946_; 
v_one_1943_ = lean_unsigned_to_nat(1u);
v_n_1944_ = lean_nat_sub(v_i_1939_, v_one_1943_);
lean_dec(v_i_1939_);
v_v_1945_ = lean_array_fget_borrowed(v_a_1937_, v_n_1944_);
lean_inc_ref(v_f_1938_);
lean_inc(v_v_1945_);
v___x_1946_ = lean_apply_1(v_f_1938_, v_v_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
v_i_1939_ = v_n_1944_;
goto _start;
}
else
{
lean_object* v_val_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_f_1938_);
v_val_1948_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_val_1948_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_array_fset(v_a_1937_, v_n_1944_, v_val_1948_);
lean_dec(v_n_1944_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1957_, lean_object* v_a_1958_, lean_object* v_f_1959_, lean_object* v_i_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1958_, v_f_1959_, v_i_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1962_, lean_object* v_x_1963_){
_start:
{
switch(lean_obj_tag(v_x_1963_))
{
case 2:
{
lean_object* v_val_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_val_1964_ = lean_ctor_get(v_x_1963_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_x_1963_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v_x_1963_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_val_1964_);
lean_dec(v_x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_info_1962_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_info_1962_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_val_1964_);
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
case 3:
{
lean_object* v_rawVal_1974_; lean_object* v_val_1975_; lean_object* v_preresolved_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1984_; 
v_rawVal_1974_ = lean_ctor_get(v_x_1963_, 1);
v_val_1975_ = lean_ctor_get(v_x_1963_, 2);
v_preresolved_1976_ = lean_ctor_get(v_x_1963_, 3);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_x_1963_, 0);
lean_dec(v_unused_1985_);
v___x_1978_ = v_x_1963_;
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_preresolved_1976_);
lean_inc(v_val_1975_);
lean_inc(v_rawVal_1974_);
lean_dec(v_x_1963_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v_info_1962_);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_info_1962_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_rawVal_1974_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_val_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_preresolved_1976_);
v___x_1981_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
}
case 1:
{
lean_object* v_info_1986_; lean_object* v_kind_1987_; lean_object* v_args_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2006_; 
v_info_1986_ = lean_ctor_get(v_x_1963_, 0);
v_kind_1987_ = lean_ctor_get(v_x_1963_, 1);
v_args_1988_ = lean_ctor_get(v_x_1963_, 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1990_ = v_x_1963_;
v_isShared_1991_ = v_isSharedCheck_2006_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_args_1988_);
lean_inc(v_kind_1987_);
lean_inc(v_info_1986_);
lean_dec(v_x_1963_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2006_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_array_get_size(v_args_1988_);
v___x_1993_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1962_, v_args_1988_, v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; 
lean_del_object(v___x_1990_);
lean_dec(v_kind_1987_);
lean_dec(v_info_1986_);
v___x_1994_ = lean_box(0);
return v___x_1994_;
}
else
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_val_1995_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 2, v_val_1995_);
v___x_2000_ = v___x_1990_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_info_1986_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_kind_1987_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_val_1995_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2007_; 
lean_dec(v_x_1963_);
lean_dec(v_info_1962_);
v___x_2007_ = lean_box(0);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2008_, lean_object* v_a_2009_, lean_object* v_i_2010_){
_start:
{
lean_object* v_zero_2011_; uint8_t v_isZero_2012_; 
v_zero_2011_ = lean_unsigned_to_nat(0u);
v_isZero_2012_ = lean_nat_dec_eq(v_i_2010_, v_zero_2011_);
if (v_isZero_2012_ == 1)
{
lean_object* v___x_2013_; 
lean_dec(v_i_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_info_2008_);
v___x_2013_ = lean_box(0);
return v___x_2013_;
}
else
{
lean_object* v_one_2014_; lean_object* v_n_2015_; lean_object* v_v_2016_; lean_object* v___x_2017_; 
v_one_2014_ = lean_unsigned_to_nat(1u);
v_n_2015_ = lean_nat_sub(v_i_2010_, v_one_2014_);
lean_dec(v_i_2010_);
v_v_2016_ = lean_array_fget_borrowed(v_a_2009_, v_n_2015_);
lean_inc(v_v_2016_);
lean_inc(v_info_2008_);
v___x_2017_ = l_Lean_Syntax_setTailInfoAux(v_info_2008_, v_v_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
v_i_2010_ = v_n_2015_;
goto _start;
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_info_2008_);
v_val_2019_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2021_ = v___x_2017_;
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v___x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_array_fset(v_a_2009_, v_n_2015_, v_val_2019_);
lean_dec(v_n_2015_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2028_, lean_object* v_info_2029_){
_start:
{
lean_object* v___x_2030_; 
lean_inc(v_stx_2028_);
v___x_2030_ = l_Lean_Syntax_setTailInfoAux(v_info_2029_, v_stx_2028_);
if (lean_obj_tag(v___x_2030_) == 0)
{
return v_stx_2028_;
}
else
{
lean_object* v_val_2031_; 
lean_dec(v_stx_2028_);
v_val_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_val_2031_);
lean_dec_ref_known(v___x_2030_, 1);
return v_val_2031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Syntax_getTailInfo(v_stx_2032_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_trailing_2034_; lean_object* v_leading_2035_; lean_object* v_pos_2036_; lean_object* v_endPos_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2055_; 
v_trailing_2034_ = lean_ctor_get(v___x_2033_, 2);
v_leading_2035_ = lean_ctor_get(v___x_2033_, 0);
v_pos_2036_ = lean_ctor_get(v___x_2033_, 1);
v_endPos_2037_ = lean_ctor_get(v___x_2033_, 3);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2039_ = v___x_2033_;
v_isShared_2040_ = v_isSharedCheck_2055_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_endPos_2037_);
lean_inc(v_trailing_2034_);
lean_inc(v_pos_2036_);
lean_inc(v_leading_2035_);
lean_dec(v___x_2033_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2055_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_str_2041_; lean_object* v_startPos_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2053_; 
v_str_2041_ = lean_ctor_get(v_trailing_2034_, 0);
v_startPos_2042_ = lean_ctor_get(v_trailing_2034_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_trailing_2034_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_trailing_2034_, 2);
lean_dec(v_unused_2054_);
v___x_2044_ = v_trailing_2034_;
v_isShared_2045_ = v_isSharedCheck_2053_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_startPos_2042_);
lean_inc(v_str_2041_);
lean_dec(v_trailing_2034_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2053_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
lean_inc(v_startPos_2042_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 2, v_startPos_2042_);
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_str_2041_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_startPos_2042_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_startPos_2042_);
v___x_2047_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 2, v___x_2047_);
v___x_2049_ = v___x_2039_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_leading_2035_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_pos_2036_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_endPos_2037_);
v___x_2049_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Syntax_setTailInfo(v_stx_2032_, v___x_2049_);
return v___x_2050_;
}
}
}
}
}
else
{
lean_dec(v___x_2033_);
return v_stx_2032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2056_, lean_object* v_f_2057_, lean_object* v_i_2058_){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_array_get_size(v_a_2056_);
v___x_2060_ = lean_nat_dec_lt(v_i_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec(v_i_2058_);
lean_dec_ref(v_f_2057_);
lean_dec_ref(v_a_2056_);
v___x_2061_ = lean_box(0);
return v___x_2061_;
}
else
{
lean_object* v_v_2062_; lean_object* v___x_2063_; 
v_v_2062_ = lean_array_fget_borrowed(v_a_2056_, v_i_2058_);
lean_inc_ref(v_f_2057_);
lean_inc(v_v_2062_);
v___x_2063_ = lean_apply_1(v_f_2057_, v_v_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_nat_add(v_i_2058_, v___x_2064_);
lean_dec(v_i_2058_);
v_i_2058_ = v___x_2065_;
goto _start;
}
else
{
lean_object* v_val_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_f_2057_);
v_val_2067_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v___x_2063_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_val_2067_);
lean_dec(v___x_2063_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_array_fset(v_a_2056_, v_i_2058_, v_val_2067_);
lean_dec(v_i_2058_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2076_, lean_object* v_inst_2077_, lean_object* v_a_2078_, lean_object* v_f_2079_, lean_object* v_i_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2078_, v_f_2079_, v_i_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_inst_2083_, lean_object* v_a_2084_, lean_object* v_f_2085_, lean_object* v_i_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2082_, v_inst_2083_, v_a_2084_, v_f_2085_, v_i_2086_);
lean_dec(v_inst_2083_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2088_, lean_object* v_x_2089_){
_start:
{
switch(lean_obj_tag(v_x_2089_))
{
case 2:
{
lean_object* v_val_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2098_; 
v_val_2090_ = lean_ctor_get(v_x_2089_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_x_2089_, 0);
lean_dec(v_unused_2099_);
v___x_2092_ = v_x_2089_;
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_val_2090_);
lean_dec(v_x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_info_2088_);
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_info_2088_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_val_2090_);
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
case 3:
{
lean_object* v_rawVal_2100_; lean_object* v_val_2101_; lean_object* v_preresolved_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_rawVal_2100_ = lean_ctor_get(v_x_2089_, 1);
v_val_2101_ = lean_ctor_get(v_x_2089_, 2);
v_preresolved_2102_ = lean_ctor_get(v_x_2089_, 3);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_x_2089_, 0);
lean_dec(v_unused_2111_);
v___x_2104_ = v_x_2089_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_preresolved_2102_);
lean_inc(v_val_2101_);
lean_inc(v_rawVal_2100_);
lean_dec(v_x_2089_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v_info_2088_);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_info_2088_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_rawVal_2100_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_val_2101_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_preresolved_2102_);
v___x_2107_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
}
case 1:
{
lean_object* v_info_2112_; lean_object* v_kind_2113_; lean_object* v_args_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2132_; 
v_info_2112_ = lean_ctor_get(v_x_2089_, 0);
v_kind_2113_ = lean_ctor_get(v_x_2089_, 1);
v_args_2114_ = lean_ctor_get(v_x_2089_, 2);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2116_ = v_x_2089_;
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_args_2114_);
lean_inc(v_kind_2113_);
lean_inc(v_info_2112_);
lean_dec(v_x_2089_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2088_, v_args_2114_, v___x_2118_);
if (lean_obj_tag(v___x_2119_) == 1)
{
lean_object* v_val_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2130_; 
v_val_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2130_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_val_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2130_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 2, v_val_2120_);
v___x_2125_ = v___x_2116_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_info_2112_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_kind_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_val_2120_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2125_);
v___x_2127_ = v___x_2122_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v___x_2131_; 
lean_dec(v___x_2119_);
lean_del_object(v___x_2116_);
lean_dec(v_kind_2113_);
lean_dec(v_info_2112_);
v___x_2131_ = lean_box(0);
return v___x_2131_;
}
}
}
default: 
{
lean_object* v___x_2133_; 
lean_dec(v_x_2089_);
lean_dec(v_info_2088_);
v___x_2133_ = lean_box(0);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2134_, lean_object* v_a_2135_, lean_object* v_i_2136_){
_start:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_array_get_size(v_a_2135_);
v___x_2138_ = lean_nat_dec_lt(v_i_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
lean_dec(v_i_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_info_2134_);
v___x_2139_ = lean_box(0);
return v___x_2139_;
}
else
{
lean_object* v_v_2140_; lean_object* v___x_2141_; 
v_v_2140_ = lean_array_fget_borrowed(v_a_2135_, v_i_2136_);
lean_inc(v_v_2140_);
lean_inc(v_info_2134_);
v___x_2141_ = l_Lean_Syntax_setHeadInfoAux(v_info_2134_, v_v_2140_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_unsigned_to_nat(1u);
v___x_2143_ = lean_nat_add(v_i_2136_, v___x_2142_);
lean_dec(v_i_2136_);
v_i_2136_ = v___x_2143_;
goto _start;
}
else
{
lean_object* v_val_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_info_2134_);
v_val_2145_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2147_ = v___x_2141_;
v_isShared_2148_ = v_isSharedCheck_2153_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_val_2145_);
lean_dec(v___x_2141_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2153_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_array_fset(v_a_2135_, v_i_2136_, v_val_2145_);
lean_dec(v_i_2136_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2151_ = v___x_2147_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2154_, lean_object* v_info_2155_){
_start:
{
lean_object* v___x_2156_; 
lean_inc(v_stx_2154_);
v___x_2156_ = l_Lean_Syntax_setHeadInfoAux(v_info_2155_, v_stx_2154_);
if (lean_obj_tag(v___x_2156_) == 0)
{
return v_stx_2154_;
}
else
{
lean_object* v_val_2157_; 
lean_dec(v_stx_2154_);
v_val_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_val_2157_);
lean_dec_ref_known(v___x_2156_, 1);
return v_val_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2158_, lean_object* v_x_2159_){
_start:
{
switch(lean_obj_tag(v_x_2159_))
{
case 0:
{
lean_dec(v_info_2158_);
return v_x_2159_;
}
case 1:
{
lean_object* v_kind_2160_; lean_object* v_args_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v_kind_2160_ = lean_ctor_get(v_x_2159_, 1);
v_args_2161_ = lean_ctor_get(v_x_2159_, 2);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2159_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_x_2159_, 0);
lean_dec(v_unused_2169_);
v___x_2163_ = v_x_2159_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_args_2161_);
lean_inc(v_kind_2160_);
lean_dec(v_x_2159_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v_info_2158_);
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_info_2158_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_kind_2160_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_args_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
case 2:
{
lean_object* v_val_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_val_2170_ = lean_ctor_get(v_x_2159_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_x_2159_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_x_2159_, 0);
lean_dec(v_unused_2178_);
v___x_2172_ = v_x_2159_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_val_2170_);
lean_dec(v_x_2159_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v_info_2158_);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_info_2158_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_val_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
default: 
{
lean_object* v_rawVal_2179_; lean_object* v_val_2180_; lean_object* v_preresolved_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_rawVal_2179_ = lean_ctor_get(v_x_2159_, 1);
v_val_2180_ = lean_ctor_get(v_x_2159_, 2);
v_preresolved_2181_ = lean_ctor_get(v_x_2159_, 3);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2159_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v_x_2159_, 0);
lean_dec(v_unused_2189_);
v___x_2183_ = v_x_2159_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_preresolved_2181_);
lean_inc(v_val_2180_);
lean_inc(v_rawVal_2179_);
lean_dec(v_x_2159_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v_info_2158_);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_info_2158_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_rawVal_2179_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_val_2180_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_preresolved_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2193_){
_start:
{
switch(lean_obj_tag(v_x_2193_))
{
case 2:
{
lean_object* v_info_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; 
v_info_2194_ = lean_ctor_get(v_x_2193_, 0);
v___x_2195_ = 0;
v___x_2196_ = l_Lean_SourceInfo_getPos_x3f(v_info_2194_, v___x_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2197_; 
lean_dec_ref_known(v_x_2193_, 2);
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
lean_ctor_set(v___x_2199_, 0, v_x_2193_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_x_2193_);
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
case 3:
{
lean_object* v_info_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; 
v_info_2206_ = lean_ctor_get(v_x_2193_, 0);
v___x_2207_ = 0;
v___x_2208_ = l_Lean_SourceInfo_getPos_x3f(v_info_2206_, v___x_2207_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref_known(v_x_2193_, 4);
v___x_2209_ = lean_box(0);
return v___x_2209_;
}
else
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2208_, 0);
lean_dec(v_unused_2217_);
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_x_2193_);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_x_2193_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
case 1:
{
lean_object* v_info_2218_; 
v_info_2218_ = lean_ctor_get(v_x_2193_, 0);
if (lean_obj_tag(v_info_2218_) == 2)
{
lean_object* v_args_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; size_t v_sz_2222_; size_t v___x_2223_; lean_object* v___x_2224_; lean_object* v_fst_2225_; 
v_args_2219_ = lean_ctor_get(v_x_2193_, 2);
lean_inc_ref(v_args_2219_);
lean_dec_ref_known(v_x_2193_, 3);
v___x_2220_ = lean_box(0);
v___x_2221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2222_ = lean_array_size(v_args_2219_);
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2219_, v_sz_2222_, v___x_2223_, v___x_2221_);
lean_dec_ref(v_args_2219_);
v_fst_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_fst_2225_);
lean_dec_ref(v___x_2224_);
if (lean_obj_tag(v_fst_2225_) == 0)
{
return v___x_2220_;
}
else
{
lean_object* v_val_2226_; 
v_val_2226_ = lean_ctor_get(v_fst_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v_fst_2225_, 1);
return v_val_2226_;
}
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2227_, 0, v_x_2193_);
return v___x_2227_;
}
}
default: 
{
lean_object* v___x_2228_; 
lean_dec(v_x_2193_);
v___x_2228_ = lean_box(0);
return v___x_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2229_, size_t v_sz_2230_, size_t v_i_2231_, lean_object* v_b_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_usize_dec_lt(v_i_2231_, v_sz_2230_);
if (v___x_2233_ == 0)
{
lean_inc_ref(v_b_2232_);
return v_b_2232_;
}
else
{
lean_object* v___x_2234_; lean_object* v_a_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_box(0);
v_a_2235_ = lean_array_uget_borrowed(v_as_2229_, v_i_2231_);
lean_inc(v_a_2235_);
v___x_2236_ = l_Lean_Syntax_getHead_x3f(v_a_2235_);
if (lean_obj_tag(v___x_2236_) == 1)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2234_);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; size_t v___x_2240_; size_t v___x_2241_; 
lean_dec(v___x_2236_);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = lean_usize_add(v_i_2231_, v___x_2240_);
v_i_2231_ = v___x_2241_;
v_b_2232_ = v___x_2239_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2243_, lean_object* v_sz_2244_, lean_object* v_i_2245_, lean_object* v_b_2246_){
_start:
{
size_t v_sz_boxed_2247_; size_t v_i_boxed_2248_; lean_object* v_res_2249_; 
v_sz_boxed_2247_ = lean_unbox_usize(v_sz_2244_);
lean_dec(v_sz_2244_);
v_i_boxed_2248_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2243_, v_sz_boxed_2247_, v_i_boxed_2248_, v_b_2246_);
lean_dec_ref(v_b_2246_);
lean_dec_ref(v_as_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2250_, lean_object* v_source_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = l_Lean_Syntax_getHeadInfo(v_source_2251_);
v___x_2253_ = l_Lean_Syntax_setHeadInfo(v_target_2250_, v___x_2252_);
v___x_2254_ = l_Lean_Syntax_getTailInfo(v_source_2251_);
v___x_2255_ = l_Lean_Syntax_setTailInfo(v___x_2253_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2256_, lean_object* v_source_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2256_, v_source_2257_);
lean_dec(v_source_2257_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2259_){
_start:
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = 0;
v___x_2261_ = l_Lean_SourceInfo_fromRef(v_stx_2259_, v___x_2260_);
v___x_2262_ = l_Lean_Syntax_setHeadInfo(v_stx_2259_, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2263_, lean_object* v_withRef_2264_, lean_object* v_x_2265_, lean_object* v_oldRef_2266_){
_start:
{
lean_object* v_ref_2267_; lean_object* v___x_2268_; 
v_ref_2267_ = l_Lean_replaceRef(v_val_2263_, v_oldRef_2266_);
v___x_2268_ = lean_apply_3(v_withRef_2264_, lean_box(0), v_ref_2267_, v_x_2265_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2269_, lean_object* v_withRef_2270_, lean_object* v_x_2271_, lean_object* v_oldRef_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2269_, v_withRef_2270_, v_x_2271_, v_oldRef_2272_);
lean_dec(v_oldRef_2272_);
lean_dec(v_val_2269_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2274_, lean_object* v_withRef_2275_, lean_object* v_toBind_2276_, lean_object* v_getRef_2277_, lean_object* v_____do__lift_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec(v_getRef_2277_);
lean_dec(v_toBind_2276_);
lean_dec(v_withRef_2275_);
return v_x_2274_;
}
else
{
lean_object* v_val_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v_val_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___f_2281_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2281_, 0, v_val_2280_);
lean_closure_set(v___f_2281_, 1, v_withRef_2275_);
lean_closure_set(v___f_2281_, 2, v_x_2274_);
v___x_2282_ = lean_apply_4(v_toBind_2276_, lean_box(0), lean_box(0), v_getRef_2277_, v___f_2281_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v_toBind_2286_; lean_object* v_getRef_2287_; lean_object* v_withRef_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v_toBind_2286_ = lean_ctor_get(v_inst_2283_, 1);
lean_inc_n(v_toBind_2286_, 2);
lean_dec_ref(v_inst_2283_);
v_getRef_2287_ = lean_ctor_get(v_inst_2284_, 0);
lean_inc_n(v_getRef_2287_, 2);
v_withRef_2288_ = lean_ctor_get(v_inst_2284_, 1);
lean_inc(v_withRef_2288_);
lean_dec_ref(v_inst_2284_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2289_, 0, v_x_2285_);
lean_closure_set(v___f_2289_, 1, v_withRef_2288_);
lean_closure_set(v___f_2289_, 2, v_toBind_2286_);
lean_closure_set(v___f_2289_, 3, v_getRef_2287_);
v___x_2290_ = lean_apply_4(v_toBind_2286_, lean_box(0), lean_box(0), v_getRef_2287_, v___f_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_00_u03b1_2294_, lean_object* v_x_2295_){
_start:
{
lean_object* v_toBind_2296_; lean_object* v_getRef_2297_; lean_object* v_withRef_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; 
v_toBind_2296_ = lean_ctor_get(v_inst_2292_, 1);
lean_inc_n(v_toBind_2296_, 2);
lean_dec_ref(v_inst_2292_);
v_getRef_2297_ = lean_ctor_get(v_inst_2293_, 0);
lean_inc_n(v_getRef_2297_, 2);
v_withRef_2298_ = lean_ctor_get(v_inst_2293_, 1);
lean_inc(v_withRef_2298_);
lean_dec_ref(v_inst_2293_);
v___f_2299_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2299_, 0, v_x_2295_);
lean_closure_set(v___f_2299_, 1, v_withRef_2298_);
lean_closure_set(v___f_2299_, 2, v_toBind_2296_);
lean_closure_set(v___f_2299_, 3, v_getRef_2297_);
v___x_2300_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v_getRef_2297_, v___f_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2310_, lean_object* v_k_2311_){
_start:
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2313_ = lean_name_eq(v_k_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
return v___x_2310_;
}
else
{
uint8_t v___x_2314_; 
v___x_2314_ = 0;
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2315_, lean_object* v_k_2316_){
_start:
{
uint8_t v___x_1783__boxed_2317_; uint8_t v_res_2318_; lean_object* v_r_2319_; 
v___x_1783__boxed_2317_ = lean_unbox(v___x_2315_);
v_res_2318_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2317_, v_k_2316_);
lean_dec(v_k_2316_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2321_, lean_object* v_p_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
if (lean_obj_tag(v_stx_2321_) == 1)
{
lean_object* v_info_2325_; lean_object* v_kind_2326_; lean_object* v_args_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_info_2325_ = lean_ctor_get(v_stx_2321_, 0);
v_kind_2326_ = lean_ctor_get(v_stx_2321_, 1);
v_args_2327_ = lean_ctor_get(v_stx_2321_, 2);
lean_inc(v_kind_2326_);
v___x_2328_ = lean_apply_1(v_p_2322_, v_kind_2326_);
v___x_2329_ = lean_unbox(v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_dec_ref(v_a_2323_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_stx_2321_);
lean_ctor_set(v___x_2330_, 1, v_a_2324_);
return v___x_2330_;
}
else
{
lean_object* v_methods_2331_; lean_object* v_quotContext_2332_; lean_object* v_currMacroScope_2333_; lean_object* v_currRecDepth_2334_; lean_object* v_maxRecDepth_2335_; lean_object* v_ref_2336_; lean_object* v_ref_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_methods_2331_ = lean_ctor_get(v_a_2323_, 0);
lean_inc_n(v_methods_2331_, 2);
v_quotContext_2332_ = lean_ctor_get(v_a_2323_, 1);
lean_inc_n(v_quotContext_2332_, 2);
v_currMacroScope_2333_ = lean_ctor_get(v_a_2323_, 2);
lean_inc_n(v_currMacroScope_2333_, 2);
v_currRecDepth_2334_ = lean_ctor_get(v_a_2323_, 3);
lean_inc_n(v_currRecDepth_2334_, 2);
v_maxRecDepth_2335_ = lean_ctor_get(v_a_2323_, 4);
lean_inc_n(v_maxRecDepth_2335_, 2);
v_ref_2336_ = lean_ctor_get(v_a_2323_, 5);
lean_inc(v_ref_2336_);
lean_dec_ref(v_a_2323_);
v_ref_2337_ = l_Lean_replaceRef(v_stx_2321_, v_ref_2336_);
lean_dec(v_ref_2336_);
lean_inc(v_ref_2337_);
v___x_2338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2338_, 0, v_methods_2331_);
lean_ctor_set(v___x_2338_, 1, v_quotContext_2332_);
lean_ctor_set(v___x_2338_, 2, v_currMacroScope_2333_);
lean_ctor_set(v___x_2338_, 3, v_currRecDepth_2334_);
lean_ctor_set(v___x_2338_, 4, v_maxRecDepth_2335_);
lean_ctor_set(v___x_2338_, 5, v_ref_2337_);
lean_inc_ref(v_stx_2321_);
v___x_2339_ = l_Lean_Macro_expandMacro_x3f(v_stx_2321_, v___x_2338_, v_a_2324_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
if (lean_obj_tag(v_a_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref_known(v___x_2338_, 6);
v_a_2341_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v___x_2339_, 0);
lean_dec(v_unused_2387_);
v___x_2343_ = v___x_2339_;
v_isShared_2344_ = v_isSharedCheck_2386_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2339_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2386_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint8_t v___x_2345_; 
v___x_2345_ = lean_nat_dec_eq(v_currRecDepth_2334_, v_maxRecDepth_2335_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2377_; 
lean_inc_ref(v_args_2327_);
lean_inc(v_kind_2326_);
lean_inc(v_info_2325_);
lean_del_object(v___x_2343_);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_stx_2321_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; 
v_unused_2378_ = lean_ctor_get(v_stx_2321_, 2);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_stx_2321_, 1);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_stx_2321_, 0);
lean_dec(v_unused_2380_);
v___x_2347_ = v_stx_2321_;
v_isShared_2348_ = v_isSharedCheck_2377_;
goto v_resetjp_2346_;
}
else
{
lean_dec(v_stx_2321_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2377_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; size_t v_sz_2352_; size_t v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_add(v_currRecDepth_2334_, v___x_2349_);
lean_dec(v_currRecDepth_2334_);
v___x_2351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2351_, 0, v_methods_2331_);
lean_ctor_set(v___x_2351_, 1, v_quotContext_2332_);
lean_ctor_set(v___x_2351_, 2, v_currMacroScope_2333_);
lean_ctor_set(v___x_2351_, 3, v___x_2350_);
lean_ctor_set(v___x_2351_, 4, v_maxRecDepth_2335_);
lean_ctor_set(v___x_2351_, 5, v_ref_2337_);
v_sz_2352_ = lean_array_size(v_args_2327_);
v___x_2353_ = ((size_t)0ULL);
v___x_2354_ = lean_unbox(v___x_2328_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2354_, v_sz_2352_, v___x_2353_, v_args_2327_, v___x_2351_, v_a_2341_);
lean_dec_ref_known(v___x_2351_, 6);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2367_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_a_2357_ = lean_ctor_get(v___x_2355_, 1);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2359_ = v___x_2355_;
v_isShared_2360_ = v_isSharedCheck_2367_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2367_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 2, v_a_2356_);
v___x_2362_ = v___x_2347_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_info_2325_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_kind_2326_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_a_2356_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2362_);
v___x_2364_ = v___x_2359_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_a_2357_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_del_object(v___x_2347_);
lean_dec(v_kind_2326_);
lean_dec(v_info_2325_);
v_a_2368_ = lean_ctor_get(v___x_2355_, 0);
v_a_2369_ = lean_ctor_get(v___x_2355_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2355_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_inc(v_a_2368_);
lean_dec(v___x_2355_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2368_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_dec(v_ref_2337_);
lean_dec(v_maxRecDepth_2335_);
lean_dec(v_currRecDepth_2334_);
lean_dec(v_currMacroScope_2333_);
lean_dec(v_quotContext_2332_);
lean_dec(v_methods_2331_);
v___x_2381_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_stx_2321_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2382_);
v___x_2384_ = v___x_2343_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2341_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v_val_2389_; lean_object* v___f_2390_; 
lean_inc_ref(v_a_2340_);
lean_dec(v_ref_2337_);
lean_dec(v_maxRecDepth_2335_);
lean_dec(v_currRecDepth_2334_);
lean_dec(v_currMacroScope_2333_);
lean_dec(v_quotContext_2332_);
lean_dec(v_methods_2331_);
lean_dec_ref_known(v_stx_2321_, 3);
v_a_2388_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2339_, 2);
v_val_2389_ = lean_ctor_get(v_a_2340_, 0);
lean_inc(v_val_2389_);
lean_dec_ref_known(v_a_2340_, 1);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2390_, 0, v___x_2328_);
v_stx_2321_ = v_val_2389_;
v_p_2322_ = v___f_2390_;
v_a_2323_ = v___x_2338_;
v_a_2324_ = v_a_2388_;
goto _start;
}
}
else
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref_known(v___x_2338_, 6);
lean_dec(v_ref_2337_);
lean_dec(v_maxRecDepth_2335_);
lean_dec(v_currRecDepth_2334_);
lean_dec(v_currMacroScope_2333_);
lean_dec(v_quotContext_2332_);
lean_dec(v_methods_2331_);
lean_dec_ref_known(v_stx_2321_, 3);
v_a_2392_ = lean_ctor_get(v___x_2339_, 0);
v_a_2393_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2339_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_inc(v_a_2392_);
lean_dec(v___x_2339_);
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
lean_object* v___x_2401_; 
lean_dec_ref(v_a_2323_);
lean_dec_ref(v_p_2322_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_stx_2321_);
lean_ctor_set(v___x_2401_, 1, v_a_2324_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2402_, size_t v_sz_2403_, size_t v_i_2404_, lean_object* v_bs_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_usize_dec_lt(v_i_2404_, v_sz_2403_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_bs_2405_);
lean_ctor_set(v___x_2409_, 1, v___y_2407_);
return v___x_2409_;
}
else
{
lean_object* v___x_2410_; lean_object* v___f_2411_; lean_object* v_v_2412_; lean_object* v___x_2413_; 
v___x_2410_ = lean_box(v___x_2402_);
v___f_2411_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2411_, 0, v___x_2410_);
v_v_2412_ = lean_array_uget_borrowed(v_bs_2405_, v_i_2404_);
lean_inc_ref(v___y_2406_);
lean_inc(v_v_2412_);
v___x_2413_ = l_Lean_expandMacros(v_v_2412_, v___f_2411_, v___y_2406_, v___y_2407_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v_a_2415_; lean_object* v___x_2416_; lean_object* v_bs_x27_2417_; size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
v_a_2415_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2413_, 2);
v___x_2416_ = lean_unsigned_to_nat(0u);
v_bs_x27_2417_ = lean_array_uset(v_bs_2405_, v_i_2404_, v___x_2416_);
v___x_2418_ = ((size_t)1ULL);
v___x_2419_ = lean_usize_add(v_i_2404_, v___x_2418_);
v___x_2420_ = lean_array_uset(v_bs_x27_2417_, v_i_2404_, v_a_2414_);
v_i_2404_ = v___x_2419_;
v_bs_2405_ = v___x_2420_;
v___y_2407_ = v_a_2415_;
goto _start;
}
else
{
lean_object* v_a_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec_ref(v_bs_2405_);
v_a_2422_ = lean_ctor_get(v___x_2413_, 0);
v_a_2423_ = lean_ctor_get(v___x_2413_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2413_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_inc(v_a_2422_);
lean_dec(v___x_2413_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2422_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2431_, lean_object* v_sz_2432_, lean_object* v_i_2433_, lean_object* v_bs_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_1802__boxed_2437_; size_t v_sz_boxed_2438_; size_t v_i_boxed_2439_; lean_object* v_res_2440_; 
v___x_1802__boxed_2437_ = lean_unbox(v___x_2431_);
v_sz_boxed_2438_ = lean_unbox_usize(v_sz_2432_);
lean_dec(v_sz_2432_);
v_i_boxed_2439_ = lean_unbox_usize(v_i_2433_);
lean_dec(v_i_2433_);
v_res_2440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1802__boxed_2437_, v_sz_boxed_2438_, v_i_boxed_2439_, v_bs_2434_, v___y_2435_, v___y_2436_);
lean_dec_ref(v___y_2435_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2441_, lean_object* v_val_2442_, uint8_t v_canonical_2443_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2444_ = l_Lean_SourceInfo_fromRef(v_src_2441_, v_canonical_2443_);
v___x_2445_ = 1;
lean_inc(v_val_2442_);
v___x_2446_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2442_, v___x_2445_);
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2448_ = lean_string_utf8_byte_size(v___x_2446_);
v___x_2449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2446_);
lean_ctor_set(v___x_2449_, 1, v___x_2447_);
lean_ctor_set(v___x_2449_, 2, v___x_2448_);
v___x_2450_ = lean_box(0);
v___x_2451_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2444_);
lean_ctor_set(v___x_2451_, 1, v___x_2449_);
lean_ctor_set(v___x_2451_, 2, v_val_2442_);
lean_ctor_set(v___x_2451_, 3, v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2452_, lean_object* v_val_2453_, lean_object* v_canonical_2454_){
_start:
{
uint8_t v_canonical_boxed_2455_; lean_object* v_res_2456_; 
v_canonical_boxed_2455_ = lean_unbox(v_canonical_2454_);
v_res_2456_ = l_Lean_mkIdentFrom(v_src_2452_, v_val_2453_, v_canonical_boxed_2455_);
lean_dec(v_src_2452_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2472_, lean_object* v_text_2473_, uint8_t v_canonical_2474_){
_start:
{
lean_object* v_info_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_body_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_info_2475_ = l_Lean_SourceInfo_fromRef(v_src_2472_, v_canonical_2474_);
v___x_2476_ = lean_box(2);
v___x_2477_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2475_, 2);
v___x_2478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_info_2475_);
lean_ctor_set(v___x_2478_, 1, v_text_2473_);
v___x_2479_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_info_2475_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = lean_unsigned_to_nat(2u);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___x_2481_);
lean_inc_ref(v___x_2482_);
v___x_2483_ = lean_array_push(v___x_2482_, v___x_2478_);
v___x_2484_ = lean_array_push(v___x_2483_, v___x_2480_);
v_body_2485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2485_, 0, v___x_2476_);
lean_ctor_set(v_body_2485_, 1, v___x_2477_);
lean_ctor_set(v_body_2485_, 2, v___x_2484_);
v___x_2486_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2487_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_info_2475_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_array_push(v___x_2482_, v___x_2488_);
v___x_2490_ = lean_array_push(v___x_2489_, v_body_2485_);
v___x_2491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2476_);
lean_ctor_set(v___x_2491_, 1, v___x_2486_);
lean_ctor_set(v___x_2491_, 2, v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2492_, lean_object* v_text_2493_, lean_object* v_canonical_2494_){
_start:
{
uint8_t v_canonical_boxed_2495_; lean_object* v_res_2496_; 
v_canonical_boxed_2495_ = lean_unbox(v_canonical_2494_);
v_res_2496_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2492_, v_text_2493_, v_canonical_boxed_2495_);
lean_dec(v_src_2492_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2497_){
_start:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_box(0);
v___x_2499_ = 0;
v___x_2500_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2498_, v_text_2497_, v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2501_, uint8_t v_canonical_2502_, lean_object* v_toPure_2503_, lean_object* v_____do__lift_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = l_Lean_mkIdentFrom(v_____do__lift_2504_, v_val_2501_, v_canonical_2502_);
v___x_2506_ = lean_apply_2(v_toPure_2503_, lean_box(0), v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2507_, lean_object* v_canonical_2508_, lean_object* v_toPure_2509_, lean_object* v_____do__lift_2510_){
_start:
{
uint8_t v_canonical_boxed_2511_; lean_object* v_res_2512_; 
v_canonical_boxed_2511_ = lean_unbox(v_canonical_2508_);
v_res_2512_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2507_, v_canonical_boxed_2511_, v_toPure_2509_, v_____do__lift_2510_);
lean_dec(v_____do__lift_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_val_2515_, uint8_t v_canonical_2516_){
_start:
{
lean_object* v_toApplicative_2517_; lean_object* v_toBind_2518_; lean_object* v_getRef_2519_; lean_object* v_toPure_2520_; lean_object* v___x_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; 
v_toApplicative_2517_ = lean_ctor_get(v_inst_2513_, 0);
lean_inc_ref(v_toApplicative_2517_);
v_toBind_2518_ = lean_ctor_get(v_inst_2513_, 1);
lean_inc(v_toBind_2518_);
lean_dec_ref(v_inst_2513_);
v_getRef_2519_ = lean_ctor_get(v_inst_2514_, 0);
lean_inc(v_getRef_2519_);
lean_dec_ref(v_inst_2514_);
v_toPure_2520_ = lean_ctor_get(v_toApplicative_2517_, 1);
lean_inc(v_toPure_2520_);
lean_dec_ref(v_toApplicative_2517_);
v___x_2521_ = lean_box(v_canonical_2516_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2522_, 0, v_val_2515_);
lean_closure_set(v___f_2522_, 1, v___x_2521_);
lean_closure_set(v___f_2522_, 2, v_toPure_2520_);
v___x_2523_ = lean_apply_4(v_toBind_2518_, lean_box(0), lean_box(0), v_getRef_2519_, v___f_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_val_2526_, lean_object* v_canonical_2527_){
_start:
{
uint8_t v_canonical_boxed_2528_; lean_object* v_res_2529_; 
v_canonical_boxed_2528_ = lean_unbox(v_canonical_2527_);
v_res_2529_ = l_Lean_mkIdentFromRef___redArg(v_inst_2524_, v_inst_2525_, v_val_2526_, v_canonical_boxed_2528_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_val_2533_, uint8_t v_canonical_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_mkIdentFromRef___redArg(v_inst_2531_, v_inst_2532_, v_val_2533_, v_canonical_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_val_2539_, lean_object* v_canonical_2540_){
_start:
{
uint8_t v_canonical_boxed_2541_; lean_object* v_res_2542_; 
v_canonical_boxed_2541_ = lean_unbox(v_canonical_2540_);
v_res_2542_ = l_Lean_mkIdentFromRef(v_m_2536_, v_inst_2537_, v_inst_2538_, v_val_2539_, v_canonical_boxed_2541_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2546_, lean_object* v_c_2547_, uint8_t v_canonical_2548_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_id_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2549_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2550_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2547_);
v_id_2551_ = l_Lean_addMacroScope(v___x_2549_, v_c_2547_, v___x_2550_);
v___x_2552_ = l_Lean_SourceInfo_fromRef(v_src_2546_, v_canonical_2548_);
v___x_2553_ = 1;
lean_inc(v_id_2551_);
v___x_2554_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2551_, v___x_2553_);
v___x_2555_ = lean_string_utf8_byte_size(v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2550_);
lean_ctor_set(v___x_2556_, 2, v___x_2555_);
v___x_2557_ = lean_box(0);
v___x_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_c_2547_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2557_);
v___x_2560_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2552_);
lean_ctor_set(v___x_2560_, 1, v___x_2556_);
lean_ctor_set(v___x_2560_, 2, v_id_2551_);
lean_ctor_set(v___x_2560_, 3, v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2561_, lean_object* v_c_2562_, lean_object* v_canonical_2563_){
_start:
{
uint8_t v_canonical_boxed_2564_; lean_object* v_res_2565_; 
v_canonical_boxed_2564_ = lean_unbox(v_canonical_2563_);
v_res_2565_ = l_Lean_mkCIdentFrom(v_src_2561_, v_c_2562_, v_canonical_boxed_2564_);
lean_dec(v_src_2561_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2566_, uint8_t v_canonical_2567_, lean_object* v_toPure_2568_, lean_object* v_____do__lift_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = l_Lean_mkCIdentFrom(v_____do__lift_2569_, v_c_2566_, v_canonical_2567_);
v___x_2571_ = lean_apply_2(v_toPure_2568_, lean_box(0), v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2572_, lean_object* v_canonical_2573_, lean_object* v_toPure_2574_, lean_object* v_____do__lift_2575_){
_start:
{
uint8_t v_canonical_boxed_2576_; lean_object* v_res_2577_; 
v_canonical_boxed_2576_ = lean_unbox(v_canonical_2573_);
v_res_2577_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2572_, v_canonical_boxed_2576_, v_toPure_2574_, v_____do__lift_2575_);
lean_dec(v_____do__lift_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_c_2580_, uint8_t v_canonical_2581_){
_start:
{
lean_object* v_toApplicative_2582_; lean_object* v_toBind_2583_; lean_object* v_getRef_2584_; lean_object* v_toPure_2585_; lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; 
v_toApplicative_2582_ = lean_ctor_get(v_inst_2578_, 0);
lean_inc_ref(v_toApplicative_2582_);
v_toBind_2583_ = lean_ctor_get(v_inst_2578_, 1);
lean_inc(v_toBind_2583_);
lean_dec_ref(v_inst_2578_);
v_getRef_2584_ = lean_ctor_get(v_inst_2579_, 0);
lean_inc(v_getRef_2584_);
lean_dec_ref(v_inst_2579_);
v_toPure_2585_ = lean_ctor_get(v_toApplicative_2582_, 1);
lean_inc(v_toPure_2585_);
lean_dec_ref(v_toApplicative_2582_);
v___x_2586_ = lean_box(v_canonical_2581_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2587_, 0, v_c_2580_);
lean_closure_set(v___f_2587_, 1, v___x_2586_);
lean_closure_set(v___f_2587_, 2, v_toPure_2585_);
v___x_2588_ = lean_apply_4(v_toBind_2583_, lean_box(0), lean_box(0), v_getRef_2584_, v___f_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_c_2591_, lean_object* v_canonical_2592_){
_start:
{
uint8_t v_canonical_boxed_2593_; lean_object* v_res_2594_; 
v_canonical_boxed_2593_ = lean_unbox(v_canonical_2592_);
v_res_2594_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2589_, v_inst_2590_, v_c_2591_, v_canonical_boxed_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_c_2598_, uint8_t v_canonical_2599_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2596_, v_inst_2597_, v_c_2598_, v_canonical_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_c_2604_, lean_object* v_canonical_2605_){
_start:
{
uint8_t v_canonical_boxed_2606_; lean_object* v_res_2607_; 
v_canonical_boxed_2606_ = lean_unbox(v_canonical_2605_);
v_res_2607_ = l_Lean_mkCIdentFromRef(v_m_2601_, v_inst_2602_, v_inst_2603_, v_c_2604_, v_canonical_boxed_2606_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2608_){
_start:
{
lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_box(0);
v___x_2610_ = 0;
v___x_2611_ = l_Lean_mkCIdentFrom(v___x_2609_, v_c_2608_, v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2612_){
_start:
{
lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2613_ = lean_box(2);
v___x_2614_ = 1;
lean_inc(v_val_2612_);
v___x_2615_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2612_, v___x_2614_);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_string_utf8_byte_size(v___x_2615_);
v___x_2618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2615_);
lean_ctor_set(v___x_2618_, 1, v___x_2616_);
lean_ctor_set(v___x_2618_, 2, v___x_2617_);
v___x_2619_ = lean_box(0);
v___x_2620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2613_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
lean_ctor_set(v___x_2620_, 2, v_val_2612_);
lean_ctor_set(v___x_2620_, 3, v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2624_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2626_ = lean_box(2);
v___x_2627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2625_);
lean_ctor_set(v___x_2627_, 2, v_args_2624_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2628_, lean_object* v_as_2629_, size_t v_sz_2630_, size_t v_i_2631_, lean_object* v_b_2632_){
_start:
{
uint8_t v___x_2633_; 
v___x_2633_ = lean_usize_dec_lt(v_i_2631_, v_sz_2630_);
if (v___x_2633_ == 0)
{
lean_dec(v_sep_2628_);
return v_b_2632_;
}
else
{
lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2655_; 
v_fst_2634_ = lean_ctor_get(v_b_2632_, 0);
v_snd_2635_ = lean_ctor_get(v_b_2632_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_b_2632_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2637_ = v_b_2632_;
v_isShared_2638_ = v_isSharedCheck_2655_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_snd_2635_);
lean_inc(v_fst_2634_);
lean_dec(v_b_2632_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2655_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_r_2640_; lean_object* v_i_2649_; lean_object* v_a_2650_; uint8_t v___x_2651_; 
v_i_2649_ = lean_unsigned_to_nat(0u);
v_a_2650_ = lean_array_uget_borrowed(v_as_2629_, v_i_2631_);
v___x_2651_ = lean_nat_dec_lt(v_i_2649_, v_fst_2634_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
lean_inc(v_a_2650_);
v___x_2652_ = lean_array_push(v_snd_2635_, v_a_2650_);
v_r_2640_ = v___x_2652_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_inc(v_sep_2628_);
v___x_2653_ = lean_array_push(v_snd_2635_, v_sep_2628_);
lean_inc(v_a_2650_);
v___x_2654_ = lean_array_push(v___x_2653_, v_a_2650_);
v_r_2640_ = v___x_2654_;
goto v___jp_2639_;
}
v___jp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2641_ = lean_unsigned_to_nat(1u);
v___x_2642_ = lean_nat_add(v_fst_2634_, v___x_2641_);
lean_dec(v_fst_2634_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 1, v_r_2640_);
lean_ctor_set(v___x_2637_, 0, v___x_2642_);
v___x_2644_ = v___x_2637_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_r_2640_);
v___x_2644_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
size_t v___x_2645_; size_t v___x_2646_; 
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2631_, v___x_2645_);
v_i_2631_ = v___x_2646_;
v_b_2632_ = v___x_2644_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2656_, lean_object* v_as_2657_, lean_object* v_sz_2658_, lean_object* v_i_2659_, lean_object* v_b_2660_){
_start:
{
size_t v_sz_boxed_2661_; size_t v_i_boxed_2662_; lean_object* v_res_2663_; 
v_sz_boxed_2661_ = lean_unbox_usize(v_sz_2658_);
lean_dec(v_sz_2658_);
v_i_boxed_2662_ = lean_unbox_usize(v_i_2659_);
lean_dec(v_i_2659_);
v_res_2663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2656_, v_as_2657_, v_sz_boxed_2661_, v_i_boxed_2662_, v_b_2660_);
lean_dec_ref(v_as_2657_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2669_, lean_object* v_sep_2670_){
_start:
{
lean_object* v___x_2671_; size_t v_sz_2672_; size_t v___x_2673_; lean_object* v___x_2674_; lean_object* v_snd_2675_; 
v___x_2671_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2672_ = lean_array_size(v_as_2669_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2670_, v_as_2669_, v_sz_2672_, v___x_2673_, v___x_2671_);
v_snd_2675_ = lean_ctor_get(v___x_2674_, 1);
lean_inc(v_snd_2675_);
lean_dec_ref(v___x_2674_);
return v_snd_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2676_, lean_object* v_sep_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_mkSepArray(v_as_2676_, v_sep_2677_);
lean_dec_ref(v_as_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2686_){
_start:
{
if (lean_obj_tag(v_arg_2686_) == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2687_;
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_val_2688_ = lean_ctor_get(v_arg_2686_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v_arg_2686_, 1);
v___x_2689_ = lean_unsigned_to_nat(1u);
v___x_2690_ = lean_mk_empty_array_with_capacity(v___x_2689_);
v___x_2691_ = lean_array_push(v___x_2690_, v_val_2688_);
v___x_2692_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2693_ = lean_box(2);
v___x_2694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v___x_2692_);
lean_ctor_set(v___x_2694_, 2, v___x_2691_);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2701_, uint8_t v_canonical_2702_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2703_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2704_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2705_ = l_Lean_mkAtomFrom(v_ref_2701_, v___x_2704_, v_canonical_2702_);
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_mk_empty_array_with_capacity(v___x_2706_);
v___x_2708_ = lean_array_push(v___x_2707_, v___x_2705_);
v___x_2709_ = lean_box(2);
v___x_2710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___x_2703_);
lean_ctor_set(v___x_2710_, 2, v___x_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2711_, lean_object* v_canonical_2712_){
_start:
{
uint8_t v_canonical_boxed_2713_; lean_object* v_res_2714_; 
v_canonical_boxed_2713_ = lean_unbox(v_canonical_2712_);
v_res_2714_ = l_Lean_mkHole(v_ref_2711_, v_canonical_boxed_2713_);
lean_dec(v_ref_2711_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2715_, lean_object* v_sep_2716_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2717_ = l_Lean_mkSepArray(v_a_2715_, v_sep_2716_);
v___x_2718_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2719_ = lean_box(2);
v___x_2720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2718_);
lean_ctor_set(v___x_2720_, 2, v___x_2717_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2721_, lean_object* v_sep_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Syntax_mkSep(v_a_2721_, v_sep_2722_);
lean_dec_ref(v_a_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2730_, lean_object* v_elems_2731_){
_start:
{
uint8_t v___x_2732_; 
lean_inc_ref(v_sep_2730_);
v___x_2732_ = lean_string_isempty(v_sep_2730_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = l_Lean_mkAtom(v_sep_2730_);
v___x_2734_ = l_Lean_mkSepArray(v_elems_2731_, v___x_2733_);
return v___x_2734_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec_ref(v_sep_2730_);
v___x_2735_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2736_ = l_Lean_mkSepArray(v_elems_2731_, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2737_, lean_object* v_elems_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2737_, v_elems_2738_);
lean_dec_ref(v_elems_2738_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2740_, lean_object* v_toPure_2741_, lean_object* v_sep_2742_, lean_object* v_ref_2743_){
_start:
{
lean_object* v___y_2745_; uint8_t v___x_2748_; 
lean_inc_ref(v_sep_2742_);
v___x_2748_ = lean_string_isempty(v_sep_2742_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_mkAtomFrom(v_ref_2743_, v_sep_2742_, v___x_2748_);
v___y_2745_ = v___x_2749_;
goto v___jp_2744_;
}
else
{
lean_object* v___x_2750_; 
lean_dec_ref(v_sep_2742_);
v___x_2750_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2745_ = v___x_2750_;
goto v___jp_2744_;
}
v___jp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = l_Lean_mkSepArray(v_elems_2740_, v___y_2745_);
v___x_2747_ = lean_apply_2(v_toPure_2741_, lean_box(0), v___x_2746_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2751_, lean_object* v_toPure_2752_, lean_object* v_sep_2753_, lean_object* v_ref_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2751_, v_toPure_2752_, v_sep_2753_, v_ref_2754_);
lean_dec(v_ref_2754_);
lean_dec_ref(v_elems_2751_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_sep_2758_, lean_object* v_elems_2759_){
_start:
{
lean_object* v_toApplicative_2760_; lean_object* v_toBind_2761_; lean_object* v_getRef_2762_; lean_object* v_toPure_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
v_toApplicative_2760_ = lean_ctor_get(v_inst_2756_, 0);
lean_inc_ref(v_toApplicative_2760_);
v_toBind_2761_ = lean_ctor_get(v_inst_2756_, 1);
lean_inc(v_toBind_2761_);
lean_dec_ref(v_inst_2756_);
v_getRef_2762_ = lean_ctor_get(v_inst_2757_, 0);
lean_inc(v_getRef_2762_);
lean_dec_ref(v_inst_2757_);
v_toPure_2763_ = lean_ctor_get(v_toApplicative_2760_, 1);
lean_inc(v_toPure_2763_);
lean_dec_ref(v_toApplicative_2760_);
v___f_2764_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2764_, 0, v_elems_2759_);
lean_closure_set(v___f_2764_, 1, v_toPure_2763_);
lean_closure_set(v___f_2764_, 2, v_sep_2758_);
v___x_2765_ = lean_apply_4(v_toBind_2761_, lean_box(0), lean_box(0), v_getRef_2762_, v___f_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2766_, lean_object* v_inst_2767_, lean_object* v_inst_2768_, lean_object* v_sep_2769_, lean_object* v_elems_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2767_, v_inst_2768_, v_sep_2769_, v_elems_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2772_, lean_object* v_elems_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2772_, v_elems_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2775_, lean_object* v_elems_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2775_, v_elems_2776_);
lean_dec_ref(v_elems_2776_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2778_, lean_object* v_sep_2779_, lean_object* v_elems_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2779_, v_elems_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2782_, lean_object* v_sep_2783_, lean_object* v_elems_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2782_, v_sep_2783_, v_elems_2784_);
lean_dec_ref(v_elems_2784_);
lean_dec(v_k_2782_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2786_, lean_object* v_sep_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2788_, 0, v_k_2786_);
lean_closure_set(v___x_2788_, 1, v_sep_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2795_, lean_object* v_x_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2797_ = lean_array_get_size(v_x_2796_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = lean_nat_dec_eq(v___x_2797_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2800_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2801_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2802_ = lean_box(2);
v___x_2803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___x_2801_);
lean_ctor_set(v___x_2803_, 2, v_x_2796_);
v___x_2804_ = lean_unsigned_to_nat(2u);
v___x_2805_ = lean_mk_empty_array_with_capacity(v___x_2804_);
v___x_2806_ = lean_array_push(v___x_2805_, v_fn_2795_);
v___x_2807_ = lean_array_push(v___x_2806_, v___x_2803_);
v___x_2808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2802_);
lean_ctor_set(v___x_2808_, 1, v___x_2800_);
lean_ctor_set(v___x_2808_, 2, v___x_2807_);
return v___x_2808_;
}
else
{
lean_dec_ref(v_x_2796_);
return v_fn_2795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2809_, lean_object* v_args_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = l_Lean_mkCIdent(v_fn_2809_);
v___x_2812_ = l_Lean_Syntax_mkApp(v___x_2811_, v_args_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2813_, lean_object* v_val_2814_, lean_object* v_info_2815_){
_start:
{
lean_object* v_atom_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_atom_2816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2816_, 0, v_info_2815_);
lean_ctor_set(v_atom_2816_, 1, v_val_2814_);
v___x_2817_ = lean_unsigned_to_nat(1u);
v___x_2818_ = lean_mk_empty_array_with_capacity(v___x_2817_);
v___x_2819_ = lean_array_push(v___x_2818_, v_atom_2816_);
v___x_2820_ = lean_box(2);
v___x_2821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v_kind_2813_);
lean_ctor_set(v___x_2821_, 2, v___x_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2825_, lean_object* v_info_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2828_ = l_Char_quote(v_val_2825_);
v___x_2829_ = l_Lean_Syntax_mkLit(v___x_2827_, v___x_2828_, v_info_2826_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2830_, lean_object* v_info_2831_){
_start:
{
uint32_t v_val_boxed_2832_; lean_object* v_res_2833_; 
v_val_boxed_2832_ = lean_unbox_uint32(v_val_2830_);
lean_dec(v_val_2830_);
v_res_2833_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2832_, v_info_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2837_, lean_object* v_info_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2840_ = l_String_quote(v_val_2837_);
v___x_2841_ = l_Lean_Syntax_mkLit(v___x_2839_, v___x_2840_, v_info_2838_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2845_, lean_object* v_info_2846_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2848_ = l_Lean_Syntax_mkLit(v___x_2847_, v_val_2845_, v_info_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2849_, lean_object* v_info_2850_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2852_ = l_Nat_reprFast(v_val_2849_);
v___x_2853_ = l_Lean_Syntax_mkLit(v___x_2851_, v___x_2852_, v_info_2850_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2857_, lean_object* v_info_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2860_ = l_Lean_Syntax_mkLit(v___x_2859_, v_val_2857_, v_info_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2864_, lean_object* v_info_2865_){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2867_ = l_Lean_Syntax_mkLit(v___x_2866_, v_val_2864_, v_info_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2868_, lean_object* v_i_2869_, lean_object* v_val_2870_){
_start:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_string_utf8_at_end(v_s_2868_, v_i_2869_);
if (v___x_2871_ == 0)
{
uint32_t v_c_2872_; uint32_t v___x_2873_; uint8_t v___x_2874_; 
v_c_2872_ = lean_string_utf8_get(v_s_2868_, v_i_2869_);
v___x_2873_ = 48;
v___x_2874_ = lean_uint32_dec_eq(v_c_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 49;
v___x_2876_ = lean_uint32_dec_eq(v_c_2872_, v___x_2875_);
if (v___x_2876_ == 0)
{
uint32_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = 95;
v___x_2878_ = lean_uint32_dec_eq(v_c_2872_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_val_2870_);
lean_dec(v_i_2869_);
v___x_2879_ = lean_box(0);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_string_utf8_next(v_s_2868_, v_i_2869_);
lean_dec(v_i_2869_);
v_i_2869_ = v___x_2880_;
goto _start;
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2882_ = lean_string_utf8_next(v_s_2868_, v_i_2869_);
lean_dec(v_i_2869_);
v___x_2883_ = lean_unsigned_to_nat(2u);
v___x_2884_ = lean_nat_mul(v___x_2883_, v_val_2870_);
lean_dec(v_val_2870_);
v___x_2885_ = lean_unsigned_to_nat(1u);
v___x_2886_ = lean_nat_add(v___x_2884_, v___x_2885_);
lean_dec(v___x_2884_);
v_i_2869_ = v___x_2882_;
v_val_2870_ = v___x_2886_;
goto _start;
}
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = lean_string_utf8_next(v_s_2868_, v_i_2869_);
lean_dec(v_i_2869_);
v___x_2889_ = lean_unsigned_to_nat(2u);
v___x_2890_ = lean_nat_mul(v___x_2889_, v_val_2870_);
lean_dec(v_val_2870_);
v_i_2869_ = v___x_2888_;
v_val_2870_ = v___x_2890_;
goto _start;
}
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_i_2869_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_val_2870_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2893_, lean_object* v_i_2894_, lean_object* v_val_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2893_, v_i_2894_, v_val_2895_);
lean_dec_ref(v_s_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2897_, lean_object* v_i_2898_, lean_object* v_val_2899_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_string_utf8_at_end(v_s_2897_, v_i_2898_);
if (v___x_2900_ == 0)
{
uint32_t v_c_2901_; uint8_t v___y_2903_; uint32_t v___x_2917_; uint8_t v___x_2918_; 
v_c_2901_ = lean_string_utf8_get(v_s_2897_, v_i_2898_);
v___x_2917_ = 48;
v___x_2918_ = lean_uint32_dec_le(v___x_2917_, v_c_2901_);
if (v___x_2918_ == 0)
{
v___y_2903_ = v___x_2900_;
goto v___jp_2902_;
}
else
{
uint32_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = 55;
v___x_2920_ = lean_uint32_dec_le(v_c_2901_, v___x_2919_);
v___y_2903_ = v___x_2920_;
goto v___jp_2902_;
}
v___jp_2902_:
{
if (v___y_2903_ == 0)
{
uint32_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = 95;
v___x_2905_ = lean_uint32_dec_eq(v_c_2901_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec(v_val_2899_);
lean_dec(v_i_2898_);
v___x_2906_ = lean_box(0);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_string_utf8_next(v_s_2897_, v_i_2898_);
lean_dec(v_i_2898_);
v_i_2898_ = v___x_2907_;
goto _start;
}
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2909_ = lean_string_utf8_next(v_s_2897_, v_i_2898_);
lean_dec(v_i_2898_);
v___x_2910_ = lean_unsigned_to_nat(8u);
v___x_2911_ = lean_nat_mul(v___x_2910_, v_val_2899_);
lean_dec(v_val_2899_);
v___x_2912_ = lean_uint32_to_nat(v_c_2901_);
v___x_2913_ = lean_nat_add(v___x_2911_, v___x_2912_);
lean_dec(v___x_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_unsigned_to_nat(48u);
v___x_2915_ = lean_nat_sub(v___x_2913_, v___x_2914_);
lean_dec(v___x_2913_);
v_i_2898_ = v___x_2909_;
v_val_2899_ = v___x_2915_;
goto _start;
}
}
}
else
{
lean_object* v___x_2921_; 
lean_dec(v_i_2898_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_val_2899_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2922_, lean_object* v_i_2923_, lean_object* v_val_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2922_, v_i_2923_, v_val_2924_);
lean_dec_ref(v_s_2922_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2926_, lean_object* v_i_2927_){
_start:
{
uint32_t v_c_2928_; lean_object* v_i_2929_; uint32_t v___x_2956_; uint8_t v___x_2957_; 
v_c_2928_ = lean_string_utf8_get(v_s_2926_, v_i_2927_);
v_i_2929_ = lean_string_utf8_next(v_s_2926_, v_i_2927_);
v___x_2956_ = 48;
v___x_2957_ = lean_uint32_dec_le(v___x_2956_, v_c_2928_);
if (v___x_2957_ == 0)
{
goto v___jp_2944_;
}
else
{
uint32_t v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = 57;
v___x_2959_ = lean_uint32_dec_le(v_c_2928_, v___x_2958_);
if (v___x_2959_ == 0)
{
goto v___jp_2944_;
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2960_ = lean_uint32_to_nat(v_c_2928_);
v___x_2961_ = lean_unsigned_to_nat(48u);
v___x_2962_ = lean_nat_sub(v___x_2960_, v___x_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v_i_2929_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
}
v___jp_2930_:
{
uint32_t v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = 65;
v___x_2932_ = lean_uint32_dec_le(v___x_2931_, v_c_2928_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
lean_dec(v_i_2929_);
v___x_2933_ = lean_box(0);
return v___x_2933_;
}
else
{
uint32_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = 70;
v___x_2935_ = lean_uint32_dec_le(v_c_2928_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec(v_i_2929_);
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2937_ = lean_unsigned_to_nat(10u);
v___x_2938_ = lean_uint32_to_nat(v_c_2928_);
v___x_2939_ = lean_nat_add(v___x_2937_, v___x_2938_);
lean_dec(v___x_2938_);
v___x_2940_ = lean_unsigned_to_nat(65u);
v___x_2941_ = lean_nat_sub(v___x_2939_, v___x_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_i_2929_);
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
}
v___jp_2944_:
{
uint32_t v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = 97;
v___x_2946_ = lean_uint32_dec_le(v___x_2945_, v_c_2928_);
if (v___x_2946_ == 0)
{
goto v___jp_2930_;
}
else
{
uint32_t v___x_2947_; uint8_t v___x_2948_; 
v___x_2947_ = 102;
v___x_2948_ = lean_uint32_dec_le(v_c_2928_, v___x_2947_);
if (v___x_2948_ == 0)
{
goto v___jp_2930_;
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2949_ = lean_unsigned_to_nat(10u);
v___x_2950_ = lean_uint32_to_nat(v_c_2928_);
v___x_2951_ = lean_nat_add(v___x_2949_, v___x_2950_);
lean_dec(v___x_2950_);
v___x_2952_ = lean_unsigned_to_nat(97u);
v___x_2953_ = lean_nat_sub(v___x_2951_, v___x_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v_i_2929_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2965_, lean_object* v_i_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2965_, v_i_2966_);
lean_dec(v_i_2966_);
lean_dec_ref(v_s_2965_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2968_, lean_object* v_i_2969_, lean_object* v_val_2970_){
_start:
{
uint8_t v___x_2971_; 
v___x_2971_ = lean_string_utf8_at_end(v_s_2968_, v_i_2969_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2968_, v_i_2969_);
if (lean_obj_tag(v___x_2972_) == 0)
{
uint32_t v___x_2973_; uint32_t v___x_2974_; uint8_t v___x_2975_; 
v___x_2973_ = lean_string_utf8_get(v_s_2968_, v_i_2969_);
v___x_2974_ = 95;
v___x_2975_ = lean_uint32_dec_eq(v___x_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v_val_2970_);
lean_dec(v_i_2969_);
v___x_2976_ = lean_box(0);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_string_utf8_next(v_s_2968_, v_i_2969_);
lean_dec(v_i_2969_);
v_i_2969_ = v___x_2977_;
goto _start;
}
}
else
{
lean_object* v_val_2979_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec(v_i_2969_);
v_val_2979_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v___x_2972_, 1);
v_fst_2980_ = lean_ctor_get(v_val_2979_, 0);
lean_inc(v_fst_2980_);
v_snd_2981_ = lean_ctor_get(v_val_2979_, 1);
lean_inc(v_snd_2981_);
lean_dec(v_val_2979_);
v___x_2982_ = lean_unsigned_to_nat(16u);
v___x_2983_ = lean_nat_mul(v___x_2982_, v_val_2970_);
lean_dec(v_val_2970_);
v___x_2984_ = lean_nat_add(v___x_2983_, v_fst_2980_);
lean_dec(v_fst_2980_);
lean_dec(v___x_2983_);
v_i_2969_ = v_snd_2981_;
v_val_2970_ = v___x_2984_;
goto _start;
}
}
else
{
lean_object* v___x_2986_; 
lean_dec(v_i_2969_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_val_2970_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_2987_, lean_object* v_i_2988_, lean_object* v_val_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2987_, v_i_2988_, v_val_2989_);
lean_dec_ref(v_s_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_2991_, lean_object* v_i_2992_, lean_object* v_val_2993_){
_start:
{
uint8_t v___x_2994_; 
v___x_2994_ = lean_string_utf8_at_end(v_s_2991_, v_i_2992_);
if (v___x_2994_ == 0)
{
uint32_t v_c_2995_; uint8_t v___y_2997_; uint32_t v___x_3011_; uint8_t v___x_3012_; 
v_c_2995_ = lean_string_utf8_get(v_s_2991_, v_i_2992_);
v___x_3011_ = 48;
v___x_3012_ = lean_uint32_dec_le(v___x_3011_, v_c_2995_);
if (v___x_3012_ == 0)
{
v___y_2997_ = v___x_2994_;
goto v___jp_2996_;
}
else
{
uint32_t v___x_3013_; uint8_t v___x_3014_; 
v___x_3013_ = 57;
v___x_3014_ = lean_uint32_dec_le(v_c_2995_, v___x_3013_);
v___y_2997_ = v___x_3014_;
goto v___jp_2996_;
}
v___jp_2996_:
{
if (v___y_2997_ == 0)
{
uint32_t v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = 95;
v___x_2999_ = lean_uint32_dec_eq(v_c_2995_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v_val_2993_);
lean_dec(v_i_2992_);
v___x_3000_ = lean_box(0);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_string_utf8_next(v_s_2991_, v_i_2992_);
lean_dec(v_i_2992_);
v_i_2992_ = v___x_3001_;
goto _start;
}
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3003_ = lean_string_utf8_next(v_s_2991_, v_i_2992_);
lean_dec(v_i_2992_);
v___x_3004_ = lean_unsigned_to_nat(10u);
v___x_3005_ = lean_nat_mul(v___x_3004_, v_val_2993_);
lean_dec(v_val_2993_);
v___x_3006_ = lean_uint32_to_nat(v_c_2995_);
v___x_3007_ = lean_nat_add(v___x_3005_, v___x_3006_);
lean_dec(v___x_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_unsigned_to_nat(48u);
v___x_3009_ = lean_nat_sub(v___x_3007_, v___x_3008_);
lean_dec(v___x_3007_);
v_i_2992_ = v___x_3003_;
v_val_2993_ = v___x_3009_;
goto _start;
}
}
}
else
{
lean_object* v___x_3015_; 
lean_dec(v_i_2992_);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_val_2993_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3016_, lean_object* v_i_3017_, lean_object* v_val_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3016_, v_i_3017_, v_val_3018_);
lean_dec_ref(v_s_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3022_){
_start:
{
lean_object* v_len_3023_; lean_object* v___x_3024_; uint8_t v___x_3034_; 
v_len_3023_ = lean_string_length(v_s_3022_);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3034_ = lean_nat_dec_eq(v_len_3023_, v___x_3024_);
if (v___x_3034_ == 0)
{
uint32_t v_c_3035_; uint32_t v___x_3036_; uint8_t v___x_3037_; 
v_c_3035_ = lean_string_utf8_get(v_s_3022_, v___x_3024_);
v___x_3036_ = 48;
v___x_3037_ = lean_uint32_dec_eq(v_c_3035_, v___x_3036_);
if (v___x_3037_ == 0)
{
uint8_t v___x_3038_; 
lean_dec(v_len_3023_);
v___x_3038_ = lean_uint32_dec_le(v___x_3036_, v_c_3035_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_box(0);
return v___x_3039_;
}
else
{
uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = 57;
v___x_3041_ = lean_uint32_dec_le(v_c_3035_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_box(0);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3022_, v___x_3024_, v___x_3024_);
return v___x_3043_;
}
}
}
else
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = lean_unsigned_to_nat(1u);
v___x_3045_ = lean_nat_dec_eq(v_len_3023_, v___x_3044_);
lean_dec(v_len_3023_);
if (v___x_3045_ == 0)
{
uint32_t v_c_3046_; uint32_t v___x_3047_; uint8_t v___x_3048_; 
v_c_3046_ = lean_string_utf8_get(v_s_3022_, v___x_3044_);
v___x_3047_ = 120;
v___x_3048_ = lean_uint32_dec_eq(v_c_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
uint32_t v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = 88;
v___x_3050_ = lean_uint32_dec_eq(v_c_3046_, v___x_3049_);
if (v___x_3050_ == 0)
{
uint32_t v___x_3051_; uint8_t v___x_3052_; 
v___x_3051_ = 98;
v___x_3052_ = lean_uint32_dec_eq(v_c_3046_, v___x_3051_);
if (v___x_3052_ == 0)
{
uint32_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = 66;
v___x_3054_ = lean_uint32_dec_eq(v_c_3046_, v___x_3053_);
if (v___x_3054_ == 0)
{
uint32_t v___x_3055_; uint8_t v___x_3056_; 
v___x_3055_ = 111;
v___x_3056_ = lean_uint32_dec_eq(v_c_3046_, v___x_3055_);
if (v___x_3056_ == 0)
{
uint32_t v___x_3057_; uint8_t v___x_3058_; 
v___x_3057_ = 79;
v___x_3058_ = lean_uint32_dec_eq(v_c_3046_, v___x_3057_);
if (v___x_3058_ == 0)
{
uint8_t v___x_3059_; 
v___x_3059_ = lean_uint32_dec_le(v___x_3036_, v_c_3046_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_box(0);
return v___x_3060_;
}
else
{
uint32_t v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = 57;
v___x_3062_ = lean_uint32_dec_le(v_c_3046_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3022_, v___x_3024_, v___x_3024_);
return v___x_3064_;
}
}
}
else
{
goto v___jp_3025_;
}
}
else
{
goto v___jp_3025_;
}
}
else
{
goto v___jp_3028_;
}
}
else
{
goto v___jp_3028_;
}
}
else
{
goto v___jp_3031_;
}
}
else
{
goto v___jp_3031_;
}
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3065_;
}
}
}
else
{
lean_object* v___x_3066_; 
lean_dec(v_len_3023_);
v___x_3066_ = lean_box(0);
return v___x_3066_;
}
v___jp_3025_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_unsigned_to_nat(2u);
v___x_3027_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3022_, v___x_3026_, v___x_3024_);
return v___x_3027_;
}
v___jp_3028_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_unsigned_to_nat(2u);
v___x_3030_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3022_, v___x_3029_, v___x_3024_);
return v___x_3030_;
}
v___jp_3031_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_unsigned_to_nat(2u);
v___x_3033_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3022_, v___x_3032_, v___x_3024_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3067_);
lean_dec_ref(v_s_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3069_, lean_object* v_stx_3070_){
_start:
{
if (lean_obj_tag(v_stx_3070_) == 1)
{
lean_object* v_kind_3071_; lean_object* v_args_3072_; uint8_t v___y_3074_; uint8_t v___x_3081_; 
v_kind_3071_ = lean_ctor_get(v_stx_3070_, 1);
v_args_3072_ = lean_ctor_get(v_stx_3070_, 2);
v___x_3081_ = lean_name_eq(v_kind_3071_, v_litKind_3069_);
if (v___x_3081_ == 0)
{
v___y_3074_ = v___x_3081_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3082_ = lean_array_get_size(v_args_3072_);
v___x_3083_ = lean_unsigned_to_nat(1u);
v___x_3084_ = lean_nat_dec_eq(v___x_3082_, v___x_3083_);
v___y_3074_ = v___x_3084_;
goto v___jp_3073_;
}
v___jp_3073_:
{
if (v___y_3074_ == 0)
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_box(0);
return v___x_3075_;
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = lean_array_fget_borrowed(v_args_3072_, v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 2)
{
lean_object* v_val_3078_; lean_object* v___x_3079_; 
v_val_3078_ = lean_ctor_get(v___x_3077_, 1);
lean_inc_ref(v_val_3078_);
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_val_3078_);
return v___x_3079_;
}
else
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
}
}
}
else
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_box(0);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3086_, lean_object* v_stx_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Syntax_isLit_x3f(v_litKind_3086_, v_stx_3087_);
lean_dec(v_stx_3087_);
lean_dec(v_litKind_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3089_, lean_object* v_stx_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_Syntax_isLit_x3f(v_litKind_3089_, v_stx_3090_);
if (lean_obj_tag(v___x_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3093_; 
v_val_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v___x_3093_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3092_);
lean_dec(v_val_3092_);
return v___x_3093_;
}
else
{
lean_object* v___x_3094_; 
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
return v___x_3094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3095_, lean_object* v_stx_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3095_, v_stx_3096_);
lean_dec(v_stx_3096_);
lean_dec(v_litKind_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3100_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3099_, v_s_3098_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_Syntax_isNatLit_x3f(v_s_3101_);
lean_dec(v_s_3101_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3108_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3107_, v_s_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3109_);
lean_dec(v_s_3109_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3111_, lean_object* v_i_3112_, lean_object* v_val_3113_, lean_object* v_e_3114_, uint8_t v_sign_3115_, lean_object* v_exp_3116_){
_start:
{
uint8_t v___x_3117_; 
v___x_3117_ = lean_string_utf8_at_end(v_s_3111_, v_i_3112_);
if (v___x_3117_ == 0)
{
uint32_t v_c_3118_; uint8_t v___y_3120_; uint32_t v___x_3134_; uint8_t v___x_3135_; 
v_c_3118_ = lean_string_utf8_get(v_s_3111_, v_i_3112_);
v___x_3134_ = 48;
v___x_3135_ = lean_uint32_dec_le(v___x_3134_, v_c_3118_);
if (v___x_3135_ == 0)
{
v___y_3120_ = v___x_3117_;
goto v___jp_3119_;
}
else
{
uint32_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = 57;
v___x_3137_ = lean_uint32_dec_le(v_c_3118_, v___x_3136_);
v___y_3120_ = v___x_3137_;
goto v___jp_3119_;
}
v___jp_3119_:
{
if (v___y_3120_ == 0)
{
uint32_t v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = 95;
v___x_3122_ = lean_uint32_dec_eq(v_c_3118_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec(v_exp_3116_);
lean_dec(v_val_3113_);
lean_dec(v_i_3112_);
v___x_3123_ = lean_box(0);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_string_utf8_next(v_s_3111_, v_i_3112_);
lean_dec(v_i_3112_);
v_i_3112_ = v___x_3124_;
goto _start;
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3126_ = lean_string_utf8_next(v_s_3111_, v_i_3112_);
lean_dec(v_i_3112_);
v___x_3127_ = lean_unsigned_to_nat(10u);
v___x_3128_ = lean_nat_mul(v___x_3127_, v_exp_3116_);
lean_dec(v_exp_3116_);
v___x_3129_ = lean_uint32_to_nat(v_c_3118_);
v___x_3130_ = lean_nat_add(v___x_3128_, v___x_3129_);
lean_dec(v___x_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_unsigned_to_nat(48u);
v___x_3132_ = lean_nat_sub(v___x_3130_, v___x_3131_);
lean_dec(v___x_3130_);
v_i_3112_ = v___x_3126_;
v_exp_3116_ = v___x_3132_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3112_);
if (v_sign_3115_ == 0)
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_le(v_e_3114_, v_exp_3116_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3139_ = lean_nat_sub(v_e_3114_, v_exp_3116_);
lean_dec(v_exp_3116_);
v___x_3140_ = lean_box(v___x_3117_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3139_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_val_3113_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3144_ = lean_nat_sub(v_exp_3116_, v_e_3114_);
lean_dec(v_exp_3116_);
v___x_3145_ = lean_box(v_sign_3115_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v___x_3144_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_val_3113_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = lean_nat_add(v_exp_3116_, v_e_3114_);
lean_dec(v_exp_3116_);
v___x_3150_ = lean_box(v_sign_3115_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3149_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_val_3113_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3154_, lean_object* v_i_3155_, lean_object* v_val_3156_, lean_object* v_e_3157_, lean_object* v_sign_3158_, lean_object* v_exp_3159_){
_start:
{
uint8_t v_sign_boxed_3160_; lean_object* v_res_3161_; 
v_sign_boxed_3160_ = lean_unbox(v_sign_3158_);
v_res_3161_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3154_, v_i_3155_, v_val_3156_, v_e_3157_, v_sign_boxed_3160_, v_exp_3159_);
lean_dec(v_e_3157_);
lean_dec_ref(v_s_3154_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3162_, lean_object* v_i_3163_, lean_object* v_val_3164_, lean_object* v_e_3165_){
_start:
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_string_utf8_at_end(v_s_3162_, v_i_3163_);
if (v___x_3166_ == 0)
{
uint32_t v_c_3167_; uint32_t v___x_3168_; uint8_t v___x_3169_; 
v_c_3167_ = lean_string_utf8_get(v_s_3162_, v_i_3163_);
v___x_3168_ = 45;
v___x_3169_ = lean_uint32_dec_eq(v_c_3167_, v___x_3168_);
if (v___x_3169_ == 0)
{
uint32_t v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = 43;
v___x_3171_ = lean_uint32_dec_eq(v_c_3167_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3162_, v_i_3163_, v_val_3164_, v_e_3165_, v___x_3171_, v___x_3172_);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_string_utf8_next(v_s_3162_, v_i_3163_);
lean_dec(v_i_3163_);
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3162_, v___x_3174_, v_val_3164_, v_e_3165_, v___x_3169_, v___x_3175_);
return v___x_3176_;
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_string_utf8_next(v_s_3162_, v_i_3163_);
lean_dec(v_i_3163_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3162_, v___x_3177_, v_val_3164_, v_e_3165_, v___x_3169_, v___x_3178_);
return v___x_3179_;
}
}
else
{
lean_object* v___x_3180_; 
lean_dec(v_val_3164_);
lean_dec(v_i_3163_);
v___x_3180_ = lean_box(0);
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3181_, lean_object* v_i_3182_, lean_object* v_val_3183_, lean_object* v_e_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3181_, v_i_3182_, v_val_3183_, v_e_3184_);
lean_dec(v_e_3184_);
lean_dec_ref(v_s_3181_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3186_, lean_object* v_i_3187_, lean_object* v_val_3188_, lean_object* v_e_3189_){
_start:
{
uint8_t v___x_3193_; 
v___x_3193_ = lean_string_utf8_at_end(v_s_3186_, v_i_3187_);
if (v___x_3193_ == 0)
{
uint32_t v_c_3194_; uint8_t v___y_3196_; uint32_t v___x_3216_; uint8_t v___x_3217_; 
v_c_3194_ = lean_string_utf8_get(v_s_3186_, v_i_3187_);
v___x_3216_ = 48;
v___x_3217_ = lean_uint32_dec_le(v___x_3216_, v_c_3194_);
if (v___x_3217_ == 0)
{
v___y_3196_ = v___x_3193_;
goto v___jp_3195_;
}
else
{
uint32_t v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = 57;
v___x_3219_ = lean_uint32_dec_le(v_c_3194_, v___x_3218_);
v___y_3196_ = v___x_3219_;
goto v___jp_3195_;
}
v___jp_3195_:
{
if (v___y_3196_ == 0)
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 95;
v___x_3198_ = lean_uint32_dec_eq(v_c_3194_, v___x_3197_);
if (v___x_3198_ == 0)
{
uint32_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = 101;
v___x_3200_ = lean_uint32_dec_eq(v_c_3194_, v___x_3199_);
if (v___x_3200_ == 0)
{
uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = 69;
v___x_3202_ = lean_uint32_dec_eq(v_c_3194_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec(v_e_3189_);
lean_dec(v_val_3188_);
lean_dec(v_i_3187_);
v___x_3203_ = lean_box(0);
return v___x_3203_;
}
else
{
goto v___jp_3190_;
}
}
else
{
goto v___jp_3190_;
}
}
else
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_string_utf8_next(v_s_3186_, v_i_3187_);
lean_dec(v_i_3187_);
v_i_3187_ = v___x_3204_;
goto _start;
}
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3206_ = lean_string_utf8_next(v_s_3186_, v_i_3187_);
lean_dec(v_i_3187_);
v___x_3207_ = lean_unsigned_to_nat(10u);
v___x_3208_ = lean_nat_mul(v___x_3207_, v_val_3188_);
lean_dec(v_val_3188_);
v___x_3209_ = lean_uint32_to_nat(v_c_3194_);
v___x_3210_ = lean_nat_add(v___x_3208_, v___x_3209_);
lean_dec(v___x_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_unsigned_to_nat(48u);
v___x_3212_ = lean_nat_sub(v___x_3210_, v___x_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_add(v_e_3189_, v___x_3213_);
lean_dec(v_e_3189_);
v_i_3187_ = v___x_3206_;
v_val_3188_ = v___x_3212_;
v_e_3189_ = v___x_3214_;
goto _start;
}
}
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec(v_i_3187_);
v___x_3220_ = lean_box(v___x_3193_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v_e_3189_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v_val_3188_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
v___jp_3190_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_string_utf8_next(v_s_3186_, v_i_3187_);
lean_dec(v_i_3187_);
v___x_3192_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3186_, v___x_3191_, v_val_3188_, v_e_3189_);
lean_dec(v_e_3189_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3224_, lean_object* v_i_3225_, lean_object* v_val_3226_, lean_object* v_e_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3224_, v_i_3225_, v_val_3226_, v_e_3227_);
lean_dec_ref(v_s_3224_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3229_, lean_object* v_i_3230_, lean_object* v_val_3231_){
_start:
{
uint8_t v___x_3236_; 
v___x_3236_ = lean_string_utf8_at_end(v_s_3229_, v_i_3230_);
if (v___x_3236_ == 0)
{
uint32_t v_c_3237_; uint8_t v___y_3239_; uint32_t v___x_3262_; uint8_t v___x_3263_; 
v_c_3237_ = lean_string_utf8_get(v_s_3229_, v_i_3230_);
v___x_3262_ = 48;
v___x_3263_ = lean_uint32_dec_le(v___x_3262_, v_c_3237_);
if (v___x_3263_ == 0)
{
v___y_3239_ = v___x_3236_;
goto v___jp_3238_;
}
else
{
uint32_t v___x_3264_; uint8_t v___x_3265_; 
v___x_3264_ = 57;
v___x_3265_ = lean_uint32_dec_le(v_c_3237_, v___x_3264_);
v___y_3239_ = v___x_3265_;
goto v___jp_3238_;
}
v___jp_3238_:
{
if (v___y_3239_ == 0)
{
uint32_t v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = 95;
v___x_3241_ = lean_uint32_dec_eq(v_c_3237_, v___x_3240_);
if (v___x_3241_ == 0)
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 46;
v___x_3243_ = lean_uint32_dec_eq(v_c_3237_, v___x_3242_);
if (v___x_3243_ == 0)
{
uint32_t v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = 101;
v___x_3245_ = lean_uint32_dec_eq(v_c_3237_, v___x_3244_);
if (v___x_3245_ == 0)
{
uint32_t v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = 69;
v___x_3247_ = lean_uint32_dec_eq(v_c_3237_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
lean_dec(v_val_3231_);
lean_dec(v_i_3230_);
v___x_3248_ = lean_box(0);
return v___x_3248_;
}
else
{
goto v___jp_3232_;
}
}
else
{
goto v___jp_3232_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_string_utf8_next(v_s_3229_, v_i_3230_);
lean_dec(v_i_3230_);
v___x_3250_ = lean_unsigned_to_nat(0u);
v___x_3251_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3229_, v___x_3249_, v_val_3231_, v___x_3250_);
return v___x_3251_;
}
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_string_utf8_next(v_s_3229_, v_i_3230_);
lean_dec(v_i_3230_);
v_i_3230_ = v___x_3252_;
goto _start;
}
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3254_ = lean_string_utf8_next(v_s_3229_, v_i_3230_);
lean_dec(v_i_3230_);
v___x_3255_ = lean_unsigned_to_nat(10u);
v___x_3256_ = lean_nat_mul(v___x_3255_, v_val_3231_);
lean_dec(v_val_3231_);
v___x_3257_ = lean_uint32_to_nat(v_c_3237_);
v___x_3258_ = lean_nat_add(v___x_3256_, v___x_3257_);
lean_dec(v___x_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_unsigned_to_nat(48u);
v___x_3260_ = lean_nat_sub(v___x_3258_, v___x_3259_);
lean_dec(v___x_3258_);
v_i_3230_ = v___x_3254_;
v_val_3231_ = v___x_3260_;
goto _start;
}
}
}
else
{
lean_object* v___x_3266_; 
lean_dec(v_val_3231_);
lean_dec(v_i_3230_);
v___x_3266_ = lean_box(0);
return v___x_3266_;
}
v___jp_3232_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = lean_string_utf8_next(v_s_3229_, v_i_3230_);
lean_dec(v_i_3230_);
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3229_, v___x_3233_, v_val_3231_, v___x_3234_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3267_, lean_object* v_i_3268_, lean_object* v_val_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3267_, v_i_3268_, v_val_3269_);
lean_dec_ref(v_s_3267_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3271_){
_start:
{
lean_object* v_len_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_len_3272_ = lean_string_length(v_s_3271_);
v___x_3273_ = lean_unsigned_to_nat(0u);
v___x_3274_ = lean_nat_dec_eq(v_len_3272_, v___x_3273_);
lean_dec(v_len_3272_);
if (v___x_3274_ == 0)
{
uint32_t v_c_3275_; uint32_t v___x_3276_; uint8_t v___x_3277_; 
v_c_3275_ = lean_string_utf8_get(v_s_3271_, v___x_3273_);
v___x_3276_ = 48;
v___x_3277_ = lean_uint32_dec_le(v___x_3276_, v_c_3275_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
else
{
uint32_t v___x_3279_; uint8_t v___x_3280_; 
v___x_3279_ = 57;
v___x_3280_ = lean_uint32_dec_le(v_c_3275_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3271_, v___x_3273_, v___x_3273_);
return v___x_3282_;
}
}
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_box(0);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3284_);
lean_dec_ref(v_s_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3286_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3288_ = l_Lean_Syntax_isLit_x3f(v___x_3287_, v_stx_3286_);
if (lean_obj_tag(v___x_3288_) == 1)
{
lean_object* v_val_3289_; lean_object* v___x_3290_; 
v_val_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_val_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v___x_3290_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3289_);
lean_dec(v_val_3289_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; 
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3292_);
lean_dec(v_stx_3292_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3294_){
_start:
{
switch(lean_obj_tag(v_x_3294_))
{
case 2:
{
lean_object* v_val_3295_; lean_object* v___x_3296_; 
v_val_3295_ = lean_ctor_get(v_x_3294_, 1);
lean_inc_ref(v_val_3295_);
lean_dec_ref_known(v_x_3294_, 2);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v_val_3295_);
return v___x_3296_;
}
case 3:
{
lean_object* v_rawVal_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_rawVal_3297_ = lean_ctor_get(v_x_3294_, 1);
lean_inc_ref(v_rawVal_3297_);
lean_dec_ref_known(v_x_3294_, 4);
v___x_3298_ = lean_substring_tostring(v_rawVal_3297_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
return v___x_3299_;
}
default: 
{
lean_object* v___x_3300_; 
lean_dec(v_x_3294_);
v___x_3300_ = lean_box(0);
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3301_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_unsigned_to_nat(0u);
return v___x_3303_;
}
else
{
lean_object* v_val_3304_; 
v_val_3304_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_val_3304_);
lean_dec_ref_known(v___x_3302_, 1);
return v_val_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Syntax_toNat(v_stx_3305_);
lean_dec(v_stx_3305_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = 9;
v___x_3308_ = lean_box_uint32(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = 10;
v___x_3310_ = lean_box_uint32(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = 13;
v___x_3312_ = lean_box_uint32(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = 39;
v___x_3314_ = lean_box_uint32(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = 34;
v___x_3316_ = lean_box_uint32(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = 92;
v___x_3318_ = lean_box_uint32(v___x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3319_, lean_object* v_i_3320_){
_start:
{
uint32_t v_c_3321_; lean_object* v_i_3322_; uint32_t v___x_3323_; uint8_t v___x_3324_; 
v_c_3321_ = lean_string_utf8_get(v_s_3319_, v_i_3320_);
v_i_3322_ = lean_string_utf8_next(v_s_3319_, v_i_3320_);
v___x_3323_ = 92;
v___x_3324_ = lean_uint32_dec_eq(v_c_3321_, v___x_3323_);
if (v___x_3324_ == 0)
{
uint32_t v___x_3325_; uint8_t v___x_3326_; 
v___x_3325_ = 34;
v___x_3326_ = lean_uint32_dec_eq(v_c_3321_, v___x_3325_);
if (v___x_3326_ == 0)
{
uint32_t v___x_3327_; uint8_t v___x_3328_; 
v___x_3327_ = 39;
v___x_3328_ = lean_uint32_dec_eq(v_c_3321_, v___x_3327_);
if (v___x_3328_ == 0)
{
uint32_t v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = 114;
v___x_3330_ = lean_uint32_dec_eq(v_c_3321_, v___x_3329_);
if (v___x_3330_ == 0)
{
uint32_t v___x_3331_; uint8_t v___x_3332_; 
v___x_3331_ = 110;
v___x_3332_ = lean_uint32_dec_eq(v_c_3321_, v___x_3331_);
if (v___x_3332_ == 0)
{
uint32_t v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = 116;
v___x_3334_ = lean_uint32_dec_eq(v_c_3321_, v___x_3333_);
if (v___x_3334_ == 0)
{
uint32_t v___x_3335_; uint8_t v___x_3336_; 
v___x_3335_ = 120;
v___x_3336_ = lean_uint32_dec_eq(v_c_3321_, v___x_3335_);
if (v___x_3336_ == 0)
{
uint32_t v___x_3337_; uint8_t v___x_3338_; 
v___x_3337_ = 117;
v___x_3338_ = lean_uint32_dec_eq(v_c_3321_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; 
lean_dec(v_i_3322_);
v___x_3339_ = lean_box(0);
return v___x_3339_;
}
else
{
lean_object* v___x_3340_; 
v___x_3340_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3319_, v_i_3322_);
lean_dec(v_i_3322_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_box(0);
return v___x_3341_;
}
else
{
lean_object* v_val_3342_; lean_object* v_fst_3343_; lean_object* v_snd_3344_; lean_object* v___x_3345_; 
v_val_3342_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___x_3340_, 1);
v_fst_3343_ = lean_ctor_get(v_val_3342_, 0);
lean_inc(v_fst_3343_);
v_snd_3344_ = lean_ctor_get(v_val_3342_, 1);
lean_inc(v_snd_3344_);
lean_dec(v_val_3342_);
v___x_3345_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3319_, v_snd_3344_);
lean_dec(v_snd_3344_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_dec(v_fst_3343_);
v___x_3346_ = lean_box(0);
return v___x_3346_;
}
else
{
lean_object* v_val_3347_; lean_object* v_fst_3348_; lean_object* v_snd_3349_; lean_object* v___x_3350_; 
v_val_3347_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___x_3345_, 1);
v_fst_3348_ = lean_ctor_get(v_val_3347_, 0);
lean_inc(v_fst_3348_);
v_snd_3349_ = lean_ctor_get(v_val_3347_, 1);
lean_inc(v_snd_3349_);
lean_dec(v_val_3347_);
v___x_3350_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3319_, v_snd_3349_);
lean_dec(v_snd_3349_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v___x_3351_; 
lean_dec(v_fst_3348_);
lean_dec(v_fst_3343_);
v___x_3351_ = lean_box(0);
return v___x_3351_;
}
else
{
lean_object* v_val_3352_; lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3355_; 
v_val_3352_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v___x_3350_, 1);
v_fst_3353_ = lean_ctor_get(v_val_3352_, 0);
lean_inc(v_fst_3353_);
v_snd_3354_ = lean_ctor_get(v_val_3352_, 1);
lean_inc(v_snd_3354_);
lean_dec(v_val_3352_);
v___x_3355_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3319_, v_snd_3354_);
lean_dec(v_snd_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v___x_3356_; 
lean_dec(v_fst_3353_);
lean_dec(v_fst_3348_);
lean_dec(v_fst_3343_);
v___x_3356_ = lean_box(0);
return v___x_3356_;
}
else
{
lean_object* v_val_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3382_; 
v_val_3357_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3359_ = v___x_3355_;
v_isShared_3360_ = v_isSharedCheck_3382_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_val_3357_);
lean_dec(v___x_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3382_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_fst_3361_; lean_object* v_snd_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3381_; 
v_fst_3361_ = lean_ctor_get(v_val_3357_, 0);
v_snd_3362_ = lean_ctor_get(v_val_3357_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_val_3357_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3364_ = v_val_3357_;
v_isShared_3365_ = v_isSharedCheck_3381_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_snd_3362_);
lean_inc(v_fst_3361_);
lean_dec(v_val_3357_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3381_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint32_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3366_ = lean_unsigned_to_nat(16u);
v___x_3367_ = lean_nat_mul(v___x_3366_, v_fst_3343_);
lean_dec(v_fst_3343_);
v___x_3368_ = lean_nat_add(v___x_3367_, v_fst_3348_);
lean_dec(v_fst_3348_);
lean_dec(v___x_3367_);
v___x_3369_ = lean_nat_mul(v___x_3366_, v___x_3368_);
lean_dec(v___x_3368_);
v___x_3370_ = lean_nat_add(v___x_3369_, v_fst_3353_);
lean_dec(v_fst_3353_);
lean_dec(v___x_3369_);
v___x_3371_ = lean_nat_mul(v___x_3366_, v___x_3370_);
lean_dec(v___x_3370_);
v___x_3372_ = lean_nat_add(v___x_3371_, v_fst_3361_);
lean_dec(v_fst_3361_);
lean_dec(v___x_3371_);
v___x_3373_ = l_Char_ofNat(v___x_3372_);
lean_dec(v___x_3372_);
v___x_3374_ = lean_box_uint32(v___x_3373_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3374_);
v___x_3376_ = v___x_3364_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_snd_3362_);
v___x_3376_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3376_);
v___x_3378_ = v___x_3359_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
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
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3319_, v_i_3322_);
lean_dec(v_i_3322_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_box(0);
return v___x_3384_;
}
else
{
lean_object* v_val_3385_; lean_object* v_fst_3386_; lean_object* v_snd_3387_; lean_object* v___x_3388_; 
v_val_3385_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_val_3385_);
lean_dec_ref_known(v___x_3383_, 1);
v_fst_3386_ = lean_ctor_get(v_val_3385_, 0);
lean_inc(v_fst_3386_);
v_snd_3387_ = lean_ctor_get(v_val_3385_, 1);
lean_inc(v_snd_3387_);
lean_dec(v_val_3385_);
v___x_3388_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3319_, v_snd_3387_);
lean_dec(v_snd_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v___x_3389_; 
lean_dec(v_fst_3386_);
v___x_3389_ = lean_box(0);
return v___x_3389_;
}
else
{
lean_object* v_val_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3411_; 
v_val_3390_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3392_ = v___x_3388_;
v_isShared_3393_ = v_isSharedCheck_3411_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_val_3390_);
lean_dec(v___x_3388_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3411_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_fst_3394_; lean_object* v_snd_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3410_; 
v_fst_3394_ = lean_ctor_get(v_val_3390_, 0);
v_snd_3395_ = lean_ctor_get(v_val_3390_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_val_3390_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3397_ = v_val_3390_;
v_isShared_3398_ = v_isSharedCheck_3410_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snd_3395_);
lean_inc(v_fst_3394_);
lean_dec(v_val_3390_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3410_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; uint32_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3399_ = lean_unsigned_to_nat(16u);
v___x_3400_ = lean_nat_mul(v___x_3399_, v_fst_3386_);
lean_dec(v_fst_3386_);
v___x_3401_ = lean_nat_add(v___x_3400_, v_fst_3394_);
lean_dec(v_fst_3394_);
lean_dec(v___x_3400_);
v___x_3402_ = l_Char_ofNat(v___x_3401_);
lean_dec(v___x_3401_);
v___x_3403_ = lean_box_uint32(v___x_3402_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3403_);
v___x_3405_ = v___x_3397_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_snd_3395_);
v___x_3405_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3407_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3405_);
v___x_3407_ = v___x_3392_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
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
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_i_3322_);
v___x_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v_i_3322_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v_i_3322_);
v___x_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v_i_3322_);
v___x_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v_i_3322_);
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
return v___x_3426_;
}
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v_i_3322_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3430_, lean_object* v_i_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Syntax_decodeQuotedChar(v_s_3430_, v_i_3431_);
lean_dec(v_i_3431_);
lean_dec_ref(v_s_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3433_){
_start:
{
uint32_t v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = 32;
v___x_3435_ = lean_uint32_dec_eq(v___y_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
uint32_t v___x_3436_; uint8_t v___x_3437_; 
v___x_3436_ = 9;
v___x_3437_ = lean_uint32_dec_eq(v___y_3433_, v___x_3436_);
if (v___x_3437_ == 0)
{
uint32_t v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = 13;
v___x_3439_ = lean_uint32_dec_eq(v___y_3433_, v___x_3438_);
if (v___x_3439_ == 0)
{
uint32_t v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = 10;
v___x_3441_ = lean_uint32_dec_eq(v___y_3433_, v___x_3440_);
return v___x_3441_;
}
else
{
return v___x_3439_;
}
}
else
{
return v___x_3437_;
}
}
else
{
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3442_){
_start:
{
uint32_t v___y_272__boxed_3443_; uint8_t v_res_3444_; lean_object* v_r_3445_; 
v___y_272__boxed_3443_ = lean_unbox_uint32(v___y_3442_);
lean_dec(v___y_3442_);
v_res_3444_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_272__boxed_3443_);
v_r_3445_ = lean_box(v_res_3444_);
return v_r_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3447_, lean_object* v_i_3448_){
_start:
{
lean_object* v___f_3449_; uint32_t v___x_3454_; uint32_t v___x_3455_; uint8_t v___x_3456_; 
v___f_3449_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3454_ = lean_string_utf8_get(v_s_3447_, v_i_3448_);
v___x_3455_ = 32;
v___x_3456_ = lean_uint32_dec_eq(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
uint32_t v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = 9;
v___x_3458_ = lean_uint32_dec_eq(v___x_3454_, v___x_3457_);
if (v___x_3458_ == 0)
{
uint32_t v___x_3459_; uint8_t v___x_3460_; 
v___x_3459_ = 13;
v___x_3460_ = lean_uint32_dec_eq(v___x_3454_, v___x_3459_);
if (v___x_3460_ == 0)
{
uint32_t v___x_3461_; uint8_t v___x_3462_; 
v___x_3461_ = 10;
v___x_3462_ = lean_uint32_dec_eq(v___x_3454_, v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref(v_s_3447_);
v___x_3463_ = lean_box(0);
return v___x_3463_;
}
else
{
goto v___jp_3450_;
}
}
else
{
goto v___jp_3450_;
}
}
else
{
goto v___jp_3450_;
}
}
else
{
goto v___jp_3450_;
}
v___jp_3450_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_string_utf8_next(v_s_3447_, v_i_3448_);
v___x_3452_ = lean_string_nextwhile(v_s_3447_, v___f_3449_, v___x_3451_);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3464_, lean_object* v_i_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Lean_Syntax_decodeStringGap(v_s_3464_, v_i_3465_);
lean_dec(v_i_3465_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3467_, lean_object* v_i_3468_, lean_object* v_acc_3469_){
_start:
{
uint32_t v_c_3470_; uint32_t v___x_3471_; uint8_t v___x_3472_; 
v_c_3470_ = lean_string_utf8_get(v_s_3467_, v_i_3468_);
v___x_3471_ = 34;
v___x_3472_ = lean_uint32_dec_eq(v_c_3470_, v___x_3471_);
if (v___x_3472_ == 0)
{
lean_object* v_i_3473_; uint8_t v___x_3474_; 
v_i_3473_ = lean_string_utf8_next(v_s_3467_, v_i_3468_);
lean_dec(v_i_3468_);
v___x_3474_ = lean_string_utf8_at_end(v_s_3467_, v_i_3473_);
if (v___x_3474_ == 0)
{
uint32_t v___x_3475_; uint8_t v___x_3476_; 
v___x_3475_ = 92;
v___x_3476_ = lean_uint32_dec_eq(v_c_3470_, v___x_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
v___x_3477_ = lean_string_push(v_acc_3469_, v_c_3470_);
v_i_3468_ = v_i_3473_;
v_acc_3469_ = v___x_3477_;
goto _start;
}
else
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Syntax_decodeQuotedChar(v_s_3467_, v_i_3473_);
if (lean_obj_tag(v___x_3479_) == 1)
{
lean_object* v_val_3480_; lean_object* v_fst_3481_; lean_object* v_snd_3482_; uint32_t v___x_3483_; lean_object* v___x_3484_; 
lean_dec(v_i_3473_);
v_val_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v_fst_3481_ = lean_ctor_get(v_val_3480_, 0);
lean_inc(v_fst_3481_);
v_snd_3482_ = lean_ctor_get(v_val_3480_, 1);
lean_inc(v_snd_3482_);
lean_dec(v_val_3480_);
v___x_3483_ = lean_unbox_uint32(v_fst_3481_);
lean_dec(v_fst_3481_);
v___x_3484_ = lean_string_push(v_acc_3469_, v___x_3483_);
v_i_3468_ = v_snd_3482_;
v_acc_3469_ = v___x_3484_;
goto _start;
}
else
{
lean_object* v___x_3486_; 
lean_dec(v___x_3479_);
lean_inc_ref(v_s_3467_);
v___x_3486_ = l_Lean_Syntax_decodeStringGap(v_s_3467_, v_i_3473_);
lean_dec(v_i_3473_);
if (lean_obj_tag(v___x_3486_) == 1)
{
lean_object* v_val_3487_; 
v_val_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v_i_3468_ = v_val_3487_;
goto _start;
}
else
{
lean_object* v___x_3489_; 
lean_dec(v___x_3486_);
lean_dec_ref(v_acc_3469_);
lean_dec_ref(v_s_3467_);
v___x_3489_ = lean_box(0);
return v___x_3489_;
}
}
}
}
else
{
lean_object* v___x_3490_; 
lean_dec(v_i_3473_);
lean_dec_ref(v_acc_3469_);
lean_dec_ref(v_s_3467_);
v___x_3490_ = lean_box(0);
return v___x_3490_;
}
}
else
{
lean_object* v___x_3491_; 
lean_dec(v_i_3468_);
lean_dec_ref(v_s_3467_);
v___x_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_acc_3469_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3492_, lean_object* v_i_3493_, lean_object* v_num_3494_){
_start:
{
uint32_t v_c_3495_; lean_object* v_i_3496_; uint32_t v___x_3497_; uint8_t v___x_3498_; 
v_c_3495_ = lean_string_utf8_get(v_s_3492_, v_i_3493_);
v_i_3496_ = lean_string_utf8_next(v_s_3492_, v_i_3493_);
lean_dec(v_i_3493_);
v___x_3497_ = 35;
v___x_3498_ = lean_uint32_dec_eq(v_c_3495_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3499_ = lean_string_utf8_byte_size(v_s_3492_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = lean_nat_add(v_num_3494_, v___x_3500_);
lean_dec(v_num_3494_);
v___x_3502_ = lean_nat_sub(v___x_3499_, v___x_3501_);
lean_dec(v___x_3501_);
v___x_3503_ = lean_string_utf8_extract(v_s_3492_, v_i_3496_, v___x_3502_);
lean_dec(v___x_3502_);
lean_dec(v_i_3496_);
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = lean_nat_add(v_num_3494_, v___x_3504_);
lean_dec(v_num_3494_);
v_i_3493_ = v_i_3496_;
v_num_3494_ = v___x_3505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3507_, lean_object* v_i_3508_, lean_object* v_num_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3507_, v_i_3508_, v_num_3509_);
lean_dec_ref(v_s_3507_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3511_){
_start:
{
lean_object* v___x_3512_; uint32_t v___x_3513_; uint32_t v___x_3514_; uint8_t v___x_3515_; 
v___x_3512_ = lean_unsigned_to_nat(0u);
v___x_3513_ = lean_string_utf8_get(v_s_3511_, v___x_3512_);
v___x_3514_ = 114;
v___x_3515_ = lean_uint32_dec_eq(v___x_3513_, v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3517_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3518_ = l_Lean_Syntax_decodeStrLitAux(v_s_3511_, v___x_3516_, v___x_3517_);
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3511_, v___x_3519_, v___x_3512_);
lean_dec_ref(v_s_3511_);
v___x_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3522_){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3524_ = l_Lean_Syntax_isLit_x3f(v___x_3523_, v_stx_3522_);
if (lean_obj_tag(v___x_3524_) == 1)
{
lean_object* v_val_3525_; lean_object* v___x_3526_; 
v_val_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = l_Lean_Syntax_decodeStrLit(v_val_3525_);
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; 
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
return v___x_3527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3528_);
lean_dec(v_stx_3528_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3530_){
_start:
{
lean_object* v___x_3531_; uint32_t v_c_3532_; uint32_t v___x_3533_; uint8_t v___x_3534_; 
v___x_3531_ = lean_unsigned_to_nat(1u);
v_c_3532_ = lean_string_utf8_get(v_s_3530_, v___x_3531_);
v___x_3533_ = 92;
v___x_3534_ = lean_uint32_dec_eq(v_c_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_box_uint32(v_c_3532_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
return v___x_3536_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_unsigned_to_nat(2u);
v___x_3538_ = l_Lean_Syntax_decodeQuotedChar(v_s_3530_, v___x_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_box(0);
return v___x_3539_;
}
else
{
lean_object* v_val_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
v_val_3540_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v___x_3538_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_val_3540_);
lean_dec(v___x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_fst_3544_; lean_object* v___x_3546_; 
v_fst_3544_ = lean_ctor_get(v_val_3540_, 0);
lean_inc(v_fst_3544_);
lean_dec(v_val_3540_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v_fst_3544_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_fst_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Syntax_decodeCharLit(v_s_3549_);
lean_dec_ref(v_s_3549_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3551_){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3553_ = l_Lean_Syntax_isLit_x3f(v___x_3552_, v_stx_3551_);
if (lean_obj_tag(v___x_3553_) == 1)
{
lean_object* v_val_3554_; lean_object* v___x_3555_; 
v_val_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = l_Lean_Syntax_decodeCharLit(v_val_3554_);
lean_dec(v_val_3554_);
return v___x_3555_;
}
else
{
lean_object* v___x_3556_; 
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
return v___x_3556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3557_);
lean_dec(v_stx_3557_);
return v_res_3558_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3559_){
_start:
{
uint8_t v___y_3577_; uint32_t v___x_3582_; uint8_t v___x_3583_; 
v___x_3582_ = 65;
v___x_3583_ = lean_uint32_dec_le(v___x_3582_, v___y_3559_);
if (v___x_3583_ == 0)
{
v___y_3577_ = v___x_3583_;
goto v___jp_3576_;
}
else
{
uint32_t v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = 90;
v___x_3585_ = lean_uint32_dec_le(v___y_3559_, v___x_3584_);
v___y_3577_ = v___x_3585_;
goto v___jp_3576_;
}
v___jp_3560_:
{
uint32_t v___x_3561_; uint8_t v___x_3562_; 
v___x_3561_ = 95;
v___x_3562_ = lean_uint32_dec_eq(v___y_3559_, v___x_3561_);
if (v___x_3562_ == 0)
{
uint32_t v___x_3563_; uint8_t v___x_3564_; 
v___x_3563_ = 39;
v___x_3564_ = lean_uint32_dec_eq(v___y_3559_, v___x_3563_);
if (v___x_3564_ == 0)
{
uint32_t v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = 33;
v___x_3566_ = lean_uint32_dec_eq(v___y_3559_, v___x_3565_);
if (v___x_3566_ == 0)
{
uint32_t v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = 63;
v___x_3568_ = lean_uint32_dec_eq(v___y_3559_, v___x_3567_);
if (v___x_3568_ == 0)
{
uint8_t v___x_3569_; 
v___x_3569_ = l_Lean_isLetterLike(v___y_3559_);
if (v___x_3569_ == 0)
{
uint8_t v___x_3570_; 
v___x_3570_ = l_Lean_isSubScriptAlnum(v___y_3559_);
return v___x_3570_;
}
else
{
return v___x_3569_;
}
}
else
{
return v___x_3568_;
}
}
else
{
return v___x_3566_;
}
}
else
{
return v___x_3564_;
}
}
else
{
return v___x_3562_;
}
}
v___jp_3571_:
{
uint32_t v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = 48;
v___x_3573_ = lean_uint32_dec_le(v___x_3572_, v___y_3559_);
if (v___x_3573_ == 0)
{
goto v___jp_3560_;
}
else
{
uint32_t v___x_3574_; uint8_t v___x_3575_; 
v___x_3574_ = 57;
v___x_3575_ = lean_uint32_dec_le(v___y_3559_, v___x_3574_);
if (v___x_3575_ == 0)
{
goto v___jp_3560_;
}
else
{
return v___x_3575_;
}
}
}
v___jp_3576_:
{
if (v___y_3577_ == 0)
{
uint32_t v___x_3578_; uint8_t v___x_3579_; 
v___x_3578_ = 97;
v___x_3579_ = lean_uint32_dec_le(v___x_3578_, v___y_3559_);
if (v___x_3579_ == 0)
{
goto v___jp_3571_;
}
else
{
uint32_t v___x_3580_; uint8_t v___x_3581_; 
v___x_3580_ = 122;
v___x_3581_ = lean_uint32_dec_le(v___y_3559_, v___x_3580_);
if (v___x_3581_ == 0)
{
goto v___jp_3571_;
}
else
{
return v___x_3581_;
}
}
}
else
{
return v___y_3577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3586_){
_start:
{
uint32_t v___y_533__boxed_3587_; uint8_t v_res_3588_; lean_object* v_r_3589_; 
v___y_533__boxed_3587_ = lean_unbox_uint32(v___y_3586_);
lean_dec(v___y_3586_);
v_res_3588_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_533__boxed_3587_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3590_, uint32_t v___x_3591_, uint32_t v___y_3592_){
_start:
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_uint32_dec_le(v___x_3590_, v___y_3592_);
if (v___x_3593_ == 0)
{
return v___x_3593_;
}
else
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_uint32_dec_le(v___y_3592_, v___x_3591_);
return v___x_3594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3595_, lean_object* v___x_3596_, lean_object* v___y_3597_){
_start:
{
uint32_t v___x_588__boxed_3598_; uint32_t v___x_589__boxed_3599_; uint32_t v___y_590__boxed_3600_; uint8_t v_res_3601_; lean_object* v_r_3602_; 
v___x_588__boxed_3598_ = lean_unbox_uint32(v___x_3595_);
lean_dec(v___x_3595_);
v___x_589__boxed_3599_ = lean_unbox_uint32(v___x_3596_);
lean_dec(v___x_3596_);
v___y_590__boxed_3600_ = lean_unbox_uint32(v___y_3597_);
lean_dec(v___y_3597_);
v_res_3601_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_588__boxed_3598_, v___x_589__boxed_3599_, v___y_590__boxed_3600_);
v_r_3602_ = lean_box(v_res_3601_);
return v_r_3602_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3603_, uint8_t v___x_3604_, uint32_t v_x_3605_){
_start:
{
uint32_t v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = 187;
v___x_3607_ = lean_uint32_dec_eq(v_x_3605_, v___x_3606_);
if (v___x_3607_ == 0)
{
return v___x_3603_;
}
else
{
return v___x_3604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3608_, lean_object* v___x_3609_, lean_object* v_x_3610_){
_start:
{
uint8_t v___x_601__boxed_3611_; uint8_t v___x_602__boxed_3612_; uint32_t v_x_603__boxed_3613_; uint8_t v_res_3614_; lean_object* v_r_3615_; 
v___x_601__boxed_3611_ = lean_unbox(v___x_3608_);
v___x_602__boxed_3612_ = lean_unbox(v___x_3609_);
v_x_603__boxed_3613_ = lean_unbox_uint32(v_x_3610_);
lean_dec(v_x_3610_);
v_res_3614_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_601__boxed_3611_, v___x_602__boxed_3612_, v_x_603__boxed_3613_);
v_r_3615_ = lean_box(v_res_3614_);
return v_r_3615_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = 48;
v___x_3618_ = lean_box_uint32(v___x_3617_);
return v___x_3618_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = 57;
v___x_3620_ = lean_box_uint32(v___x_3619_);
return v___x_3620_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___f_3623_; 
v___x_3621_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3622_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3623_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3623_, 0, v___x_3621_);
lean_closure_set(v___f_3623_, 1, v___x_3622_);
return v___f_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3624_, lean_object* v_acc_3625_){
_start:
{
lean_object* v_ss_3627_; lean_object* v_acc_3628_; uint8_t v___x_3637_; 
lean_inc_ref(v_ss_3624_);
v___x_3637_ = lean_substring_isempty(v_ss_3624_);
if (v___x_3637_ == 0)
{
uint32_t v_curr_3638_; uint32_t v___x_3639_; uint8_t v___x_3640_; 
lean_inc_ref(v_ss_3624_);
v_curr_3638_ = lean_substring_front(v_ss_3624_);
v___x_3639_ = 171;
v___x_3640_ = lean_uint32_dec_eq(v_curr_3638_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___f_3641_; uint8_t v___y_3673_; uint32_t v___x_3678_; uint8_t v___x_3679_; 
v___f_3641_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3678_ = 65;
v___x_3679_ = lean_uint32_dec_le(v___x_3678_, v_curr_3638_);
if (v___x_3679_ == 0)
{
v___y_3673_ = v___x_3679_;
goto v___jp_3672_;
}
else
{
uint32_t v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = 90;
v___x_3681_ = lean_uint32_dec_le(v_curr_3638_, v___x_3680_);
v___y_3673_ = v___x_3681_;
goto v___jp_3672_;
}
v___jp_3642_:
{
lean_object* v_idPart_3643_; lean_object* v_startPos_3644_; lean_object* v_stopPos_3645_; lean_object* v_startPos_3646_; lean_object* v_stopPos_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_inc_ref(v_ss_3624_);
v_idPart_3643_ = lean_substring_takewhile(v_ss_3624_, v___f_3641_);
v_startPos_3644_ = lean_ctor_get(v_idPart_3643_, 1);
v_stopPos_3645_ = lean_ctor_get(v_idPart_3643_, 2);
v_startPos_3646_ = lean_ctor_get(v_ss_3624_, 1);
v_stopPos_3647_ = lean_ctor_get(v_ss_3624_, 2);
v___x_3648_ = lean_nat_sub(v_stopPos_3645_, v_startPos_3644_);
v___x_3649_ = lean_nat_sub(v_stopPos_3647_, v_startPos_3646_);
v___x_3650_ = lean_substring_extract(v_ss_3624_, v___x_3648_, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3651_, 0, v_idPart_3643_);
lean_ctor_set(v___x_3651_, 1, v_acc_3625_);
v_ss_3627_ = v___x_3650_;
v_acc_3628_ = v___x_3651_;
goto v___jp_3626_;
}
v___jp_3652_:
{
uint32_t v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = 95;
v___x_3654_ = lean_uint32_dec_eq(v_curr_3638_, v___x_3653_);
if (v___x_3654_ == 0)
{
uint8_t v___x_3655_; 
v___x_3655_ = l_Lean_isLetterLike(v_curr_3638_);
if (v___x_3655_ == 0)
{
uint32_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3656_ = 48;
v___x_3657_ = lean_uint32_dec_le(v___x_3656_, v_curr_3638_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
lean_dec(v_acc_3625_);
lean_dec_ref(v_ss_3624_);
v___x_3658_ = lean_box(0);
return v___x_3658_;
}
else
{
uint32_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = 57;
v___x_3660_ = lean_uint32_dec_le(v_curr_3638_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec(v_acc_3625_);
lean_dec_ref(v_ss_3624_);
v___x_3661_ = lean_box(0);
return v___x_3661_;
}
else
{
lean_object* v___f_3662_; lean_object* v_idPart_3663_; lean_object* v_startPos_3664_; lean_object* v_stopPos_3665_; lean_object* v_startPos_3666_; lean_object* v_stopPos_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___f_3662_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3624_);
v_idPart_3663_ = lean_substring_takewhile(v_ss_3624_, v___f_3662_);
v_startPos_3664_ = lean_ctor_get(v_idPart_3663_, 1);
v_stopPos_3665_ = lean_ctor_get(v_idPart_3663_, 2);
v_startPos_3666_ = lean_ctor_get(v_ss_3624_, 1);
v_stopPos_3667_ = lean_ctor_get(v_ss_3624_, 2);
v___x_3668_ = lean_nat_sub(v_stopPos_3665_, v_startPos_3664_);
v___x_3669_ = lean_nat_sub(v_stopPos_3667_, v_startPos_3666_);
v___x_3670_ = lean_substring_extract(v_ss_3624_, v___x_3668_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_idPart_3663_);
lean_ctor_set(v___x_3671_, 1, v_acc_3625_);
v_ss_3627_ = v___x_3670_;
v_acc_3628_ = v___x_3671_;
goto v___jp_3626_;
}
}
}
else
{
goto v___jp_3642_;
}
}
else
{
goto v___jp_3642_;
}
}
v___jp_3672_:
{
if (v___y_3673_ == 0)
{
uint32_t v___x_3674_; uint8_t v___x_3675_; 
v___x_3674_ = 97;
v___x_3675_ = lean_uint32_dec_le(v___x_3674_, v_curr_3638_);
if (v___x_3675_ == 0)
{
goto v___jp_3652_;
}
else
{
uint32_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = 122;
v___x_3677_ = lean_uint32_dec_le(v_curr_3638_, v___x_3676_);
if (v___x_3677_ == 0)
{
goto v___jp_3652_;
}
else
{
goto v___jp_3642_;
}
}
}
else
{
goto v___jp_3642_;
}
}
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___f_3684_; lean_object* v_escapedPart_3685_; lean_object* v_str_3686_; lean_object* v_startPos_3687_; lean_object* v_stopPos_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3709_; 
v___x_3682_ = lean_box(v___x_3640_);
v___x_3683_ = lean_box(v___x_3637_);
v___f_3684_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3684_, 0, v___x_3682_);
lean_closure_set(v___f_3684_, 1, v___x_3683_);
lean_inc_ref(v_ss_3624_);
v_escapedPart_3685_ = lean_substring_takewhile(v_ss_3624_, v___f_3684_);
v_str_3686_ = lean_ctor_get(v_escapedPart_3685_, 0);
v_startPos_3687_ = lean_ctor_get(v_escapedPart_3685_, 1);
v_stopPos_3688_ = lean_ctor_get(v_escapedPart_3685_, 2);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_escapedPart_3685_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3690_ = v_escapedPart_3685_;
v_isShared_3691_ = v_isSharedCheck_3709_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_stopPos_3688_);
lean_inc(v_startPos_3687_);
lean_inc(v_str_3686_);
lean_dec(v_escapedPart_3685_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3709_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_startPos_3692_; lean_object* v_stopPos_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v_escapedPart_3697_; 
v_startPos_3692_ = lean_ctor_get(v_ss_3624_, 1);
v_stopPos_3693_ = lean_ctor_get(v_ss_3624_, 2);
v___x_3694_ = lean_string_utf8_next(v_str_3686_, v_stopPos_3688_);
lean_dec(v_stopPos_3688_);
lean_inc(v_stopPos_3693_);
v___x_3695_ = lean_string_pos_min(v_stopPos_3693_, v___x_3694_);
lean_inc(v___x_3695_);
lean_inc(v_startPos_3687_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 2, v___x_3695_);
v_escapedPart_3697_ = v___x_3690_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_str_3686_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_startPos_3687_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v___x_3695_);
v_escapedPart_3697_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; uint32_t v___x_3700_; uint32_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3698_ = lean_nat_sub(v___x_3695_, v_startPos_3687_);
lean_dec(v_startPos_3687_);
lean_dec(v___x_3695_);
lean_inc(v___x_3698_);
lean_inc_ref_n(v_escapedPart_3697_, 2);
v___x_3699_ = lean_substring_prev(v_escapedPart_3697_, v___x_3698_);
v___x_3700_ = lean_substring_get(v_escapedPart_3697_, v___x_3699_);
v___x_3701_ = 187;
v___x_3702_ = lean_uint32_dec_eq(v___x_3700_, v___x_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; 
lean_dec(v___x_3698_);
lean_dec_ref(v_escapedPart_3697_);
lean_dec(v_acc_3625_);
lean_dec_ref(v_ss_3624_);
v___x_3703_ = lean_box(0);
return v___x_3703_;
}
else
{
if (v___x_3637_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3704_ = lean_nat_sub(v_stopPos_3693_, v_startPos_3692_);
v___x_3705_ = lean_substring_extract(v_ss_3624_, v___x_3698_, v___x_3704_);
v___x_3706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3706_, 0, v_escapedPart_3697_);
lean_ctor_set(v___x_3706_, 1, v_acc_3625_);
v_ss_3627_ = v___x_3705_;
v_acc_3628_ = v___x_3706_;
goto v___jp_3626_;
}
else
{
lean_object* v___x_3707_; 
lean_dec(v___x_3698_);
lean_dec_ref(v_escapedPart_3697_);
lean_dec(v_acc_3625_);
lean_dec_ref(v_ss_3624_);
v___x_3707_ = lean_box(0);
return v___x_3707_;
}
}
}
}
}
}
else
{
lean_object* v___x_3710_; 
lean_dec(v_acc_3625_);
lean_dec_ref(v_ss_3624_);
v___x_3710_ = lean_box(0);
return v___x_3710_;
}
v___jp_3626_:
{
uint32_t v___x_3629_; uint32_t v___x_3630_; uint8_t v___x_3631_; 
lean_inc_ref(v_ss_3627_);
v___x_3629_ = lean_substring_front(v_ss_3627_);
v___x_3630_ = 46;
v___x_3631_ = lean_uint32_dec_eq(v___x_3629_, v___x_3630_);
if (v___x_3631_ == 0)
{
uint8_t v___x_3632_; 
v___x_3632_ = lean_substring_isempty(v_ss_3627_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; 
lean_dec(v_acc_3628_);
v___x_3633_ = lean_box(0);
return v___x_3633_;
}
else
{
return v_acc_3628_;
}
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_unsigned_to_nat(1u);
v___x_3635_ = lean_substring_drop(v_ss_3627_, v___x_3634_);
v_ss_3624_ = v___x_3635_;
v_acc_3625_ = v_acc_3628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = lean_box(0);
v___x_3713_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3711_, v___x_3712_);
v___x_3714_ = l_List_reverse___redArg(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3718_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3719_ = lean_unsigned_to_nat(10u);
v___x_3720_ = lean_unsigned_to_nat(1253u);
v___x_3721_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3722_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3723_ = l_mkPanicMessageWithDecl(v___x_3722_, v___x_3721_, v___x_3720_, v___x_3719_, v___x_3718_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3724_, lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 0)
{
lean_inc(v_init_3724_);
return v_init_3724_;
}
else
{
lean_object* v_head_3726_; lean_object* v_tail_3727_; lean_object* v___x_3728_; lean_object* v_comp_3729_; uint32_t v___x_3730_; uint32_t v___x_3731_; uint8_t v___x_3732_; 
v_head_3726_ = lean_ctor_get(v_x_3725_, 0);
lean_inc(v_head_3726_);
v_tail_3727_ = lean_ctor_get(v_x_3725_, 1);
lean_inc(v_tail_3727_);
lean_dec_ref_known(v_x_3725_, 2);
v___x_3728_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3724_, v_tail_3727_);
v_comp_3729_ = lean_substring_tostring(v_head_3726_);
lean_inc_ref(v_comp_3729_);
v___x_3730_ = lean_string_front(v_comp_3729_);
v___x_3731_ = 171;
v___x_3732_ = lean_uint32_dec_eq(v___x_3730_, v___x_3731_);
if (v___x_3732_ == 0)
{
uint32_t v___x_3733_; uint8_t v___x_3734_; 
v___x_3733_ = 48;
v___x_3734_ = lean_uint32_dec_le(v___x_3733_, v___x_3730_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_Name_str___override(v___x_3728_, v_comp_3729_);
return v___x_3735_;
}
else
{
uint32_t v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = 57;
v___x_3737_ = lean_uint32_dec_le(v___x_3730_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Name_str___override(v___x_3728_, v_comp_3729_);
return v___x_3738_;
}
else
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3729_);
lean_dec_ref(v_comp_3729_);
if (lean_obj_tag(v___x_3739_) == 1)
{
lean_object* v_val_3740_; lean_object* v___x_3741_; 
v_val_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_val_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = l_Lean_Name_num___override(v___x_3728_, v_val_3740_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec(v___x_3739_);
lean_dec(v___x_3728_);
v___x_3742_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3743_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3742_);
return v___x_3743_;
}
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3744_ = lean_unsigned_to_nat(1u);
v___x_3745_ = lean_string_drop(v_comp_3729_, v___x_3744_);
v___x_3746_ = lean_string_dropright(v___x_3745_, v___x_3744_);
v___x_3747_ = l_Lean_Name_str___override(v___x_3728_, v___x_3746_);
return v___x_3747_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3748_, lean_object* v_x_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3748_, v_x_3749_);
lean_dec(v_init_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3751_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3751_, v___x_3752_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_box(0);
return v___x_3754_;
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = lean_box(0);
v___x_3756_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3755_, v___x_3753_);
return v___x_3756_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3757_){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3758_ = lean_unsigned_to_nat(0u);
v___x_3759_ = lean_string_utf8_byte_size(v_s_3757_);
v___x_3760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3760_, 0, v_s_3757_);
lean_ctor_set(v___x_3760_, 1, v___x_3758_);
lean_ctor_set(v___x_3760_, 2, v___x_3759_);
v___x_3761_ = l_Substring_Raw_toName(v___x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3762_){
_start:
{
lean_object* v___x_3763_; uint32_t v___x_3764_; uint32_t v___x_3765_; uint8_t v___x_3766_; 
v___x_3763_ = lean_unsigned_to_nat(0u);
v___x_3764_ = lean_string_utf8_get(v_s_3762_, v___x_3763_);
v___x_3765_ = 96;
v___x_3766_ = lean_uint32_dec_eq(v___x_3764_, v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
lean_dec_ref(v_s_3762_);
v___x_3767_ = lean_box(0);
return v___x_3767_;
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3768_ = lean_string_utf8_byte_size(v_s_3762_);
v___x_3769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3769_, 0, v_s_3762_);
lean_ctor_set(v___x_3769_, 1, v___x_3763_);
lean_ctor_set(v___x_3769_, 2, v___x_3768_);
v___x_3770_ = lean_unsigned_to_nat(1u);
v___x_3771_ = lean_substring_drop(v___x_3769_, v___x_3770_);
v___x_3772_ = l_Substring_Raw_toName(v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_box(0);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
return v___x_3774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3775_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3777_ = l_Lean_Syntax_isLit_x3f(v___x_3776_, v_stx_3775_);
if (lean_obj_tag(v___x_3777_) == 1)
{
lean_object* v_val_3778_; lean_object* v___x_3779_; 
v_val_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_val_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___x_3779_ = l_Lean_Syntax_decodeNameLit(v_val_3778_);
return v___x_3779_;
}
else
{
lean_object* v___x_3780_; 
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
return v___x_3780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3781_);
lean_dec(v_stx_3781_);
return v_res_3782_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3783_){
_start:
{
if (lean_obj_tag(v_x_3783_) == 1)
{
lean_object* v_args_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_args_3784_ = lean_ctor_get(v_x_3783_, 2);
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = lean_array_get_size(v_args_3784_);
v___x_3787_ = lean_nat_dec_lt(v___x_3785_, v___x_3786_);
return v___x_3787_;
}
else
{
uint8_t v___x_3788_; 
v___x_3788_ = 0;
return v___x_3788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3789_){
_start:
{
uint8_t v_res_3790_; lean_object* v_r_3791_; 
v_res_3790_ = l_Lean_Syntax_hasArgs(v_x_3789_);
lean_dec(v_x_3789_);
v_r_3791_ = lean_box(v_res_3790_);
return v_r_3791_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 2)
{
uint8_t v___x_3793_; 
v___x_3793_ = 1;
return v___x_3793_;
}
else
{
uint8_t v___x_3794_; 
v___x_3794_ = 0;
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3795_){
_start:
{
uint8_t v_res_3796_; lean_object* v_r_3797_; 
v_res_3796_ = l_Lean_Syntax_isAtom(v_x_3795_);
lean_dec(v_x_3795_);
v_r_3797_ = lean_box(v_res_3796_);
return v_r_3797_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3798_, lean_object* v_x_3799_){
_start:
{
if (lean_obj_tag(v_x_3799_) == 2)
{
lean_object* v_val_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v_val_3800_ = lean_ctor_get(v_x_3799_, 1);
lean_inc_ref(v_val_3800_);
lean_dec_ref_known(v_x_3799_, 2);
v___x_3801_ = lean_string_trim(v_val_3800_);
v___x_3802_ = lean_string_trim(v_token_3798_);
v___x_3803_ = lean_string_dec_eq(v___x_3801_, v___x_3802_);
lean_dec_ref(v___x_3802_);
lean_dec_ref(v___x_3801_);
return v___x_3803_;
}
else
{
uint8_t v___x_3804_; 
lean_dec(v_x_3799_);
lean_dec_ref(v_token_3798_);
v___x_3804_ = 0;
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3805_, lean_object* v_x_3806_){
_start:
{
uint8_t v_res_3807_; lean_object* v_r_3808_; 
v_res_3807_ = l_Lean_Syntax_isToken(v_token_3805_, v_x_3806_);
v_r_3808_ = lean_box(v_res_3807_);
return v_r_3808_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3809_){
_start:
{
switch(lean_obj_tag(v_stx_3809_))
{
case 1:
{
lean_object* v_kind_3810_; lean_object* v_args_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v_kind_3810_ = lean_ctor_get(v_stx_3809_, 1);
v_args_3811_ = lean_ctor_get(v_stx_3809_, 2);
v___x_3812_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3813_ = lean_name_eq(v_kind_3810_, v___x_3812_);
if (v___x_3813_ == 0)
{
return v___x_3813_;
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3814_ = lean_array_get_size(v_args_3811_);
v___x_3815_ = lean_unsigned_to_nat(0u);
v___x_3816_ = lean_nat_dec_eq(v___x_3814_, v___x_3815_);
return v___x_3816_;
}
}
case 0:
{
uint8_t v___x_3817_; 
v___x_3817_ = 1;
return v___x_3817_;
}
default: 
{
uint8_t v___x_3818_; 
v___x_3818_ = 0;
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3819_){
_start:
{
uint8_t v_res_3820_; lean_object* v_r_3821_; 
v_res_3820_ = l_Lean_Syntax_isNone(v_stx_3819_);
lean_dec(v_stx_3819_);
v_r_3821_ = lean_box(v_res_3820_);
return v_r_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Syntax_getOptional_x3f(v_stx_3822_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_box(0);
return v___x_3824_;
}
else
{
lean_object* v_val_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3833_; 
v_val_3825_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3827_ = v___x_3823_;
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_val_3825_);
lean_dec(v___x_3823_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = l_Lean_Syntax_getId(v_val_3825_);
lean_dec(v_val_3825_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3829_);
v___x_3831_ = v___x_3827_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3834_);
lean_dec(v_stx_3834_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3836_, lean_object* v_x_3837_){
_start:
{
if (lean_obj_tag(v_x_3837_) == 1)
{
lean_object* v_args_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_args_3838_ = lean_ctor_get(v_x_3837_, 2);
lean_inc_ref(v_p_3836_);
lean_inc_ref(v_x_3837_);
v___x_3839_ = lean_apply_1(v_p_3836_, v_x_3837_);
v___x_3840_ = lean_unbox(v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; lean_object* v_fst_3846_; 
lean_inc_ref(v_args_3838_);
lean_dec_ref_known(v_x_3837_, 3);
v___x_3841_ = lean_box(0);
v___x_3842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3843_ = lean_array_size(v_args_3838_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3836_, v_args_3838_, v_sz_3843_, v___x_3844_, v___x_3842_);
lean_dec_ref(v_args_3838_);
v_fst_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_fst_3846_);
lean_dec_ref(v___x_3845_);
if (lean_obj_tag(v_fst_3846_) == 0)
{
return v___x_3841_;
}
else
{
lean_object* v_val_3847_; 
v_val_3847_ = lean_ctor_get(v_fst_3846_, 0);
lean_inc(v_val_3847_);
lean_dec_ref_known(v_fst_3846_, 1);
return v_val_3847_;
}
}
else
{
lean_object* v___x_3848_; 
lean_dec_ref(v_p_3836_);
v___x_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_x_3837_);
return v___x_3848_;
}
}
else
{
lean_object* v___x_3849_; uint8_t v___x_3850_; 
lean_inc(v_x_3837_);
v___x_3849_ = lean_apply_1(v_p_3836_, v_x_3837_);
v___x_3850_ = lean_unbox(v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; 
lean_dec(v_x_3837_);
v___x_3851_ = lean_box(0);
return v___x_3851_;
}
else
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_x_3837_);
return v___x_3852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3853_, lean_object* v_as_3854_, size_t v_sz_3855_, size_t v_i_3856_, lean_object* v_b_3857_){
_start:
{
uint8_t v___x_3858_; 
v___x_3858_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
if (v___x_3858_ == 0)
{
lean_dec_ref(v_p_3853_);
lean_inc_ref(v_b_3857_);
return v_b_3857_;
}
else
{
lean_object* v___x_3859_; lean_object* v_a_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_box(0);
v_a_3860_ = lean_array_uget_borrowed(v_as_3854_, v_i_3856_);
lean_inc(v_a_3860_);
lean_inc_ref(v_p_3853_);
v___x_3861_ = l_Lean_Syntax_findAux(v_p_3853_, v_a_3860_);
if (lean_obj_tag(v___x_3861_) == 1)
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
lean_dec_ref(v_p_3853_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v___x_3859_);
return v___x_3863_;
}
else
{
lean_object* v___x_3864_; size_t v___x_3865_; size_t v___x_3866_; 
lean_dec(v___x_3861_);
v___x_3864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_add(v_i_3856_, v___x_3865_);
v_i_3856_ = v___x_3866_;
v_b_3857_ = v___x_3864_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3868_, lean_object* v_as_3869_, lean_object* v_sz_3870_, lean_object* v_i_3871_, lean_object* v_b_3872_){
_start:
{
size_t v_sz_boxed_3873_; size_t v_i_boxed_3874_; lean_object* v_res_3875_; 
v_sz_boxed_3873_ = lean_unbox_usize(v_sz_3870_);
lean_dec(v_sz_3870_);
v_i_boxed_3874_ = lean_unbox_usize(v_i_3871_);
lean_dec(v_i_3871_);
v_res_3875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3868_, v_as_3869_, v_sz_boxed_3873_, v_i_boxed_3874_, v_b_3872_);
lean_dec_ref(v_b_3872_);
lean_dec_ref(v_as_3869_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3876_, lean_object* v_p_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Lean_Syntax_findAux(v_p_3877_, v_stx_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3879_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_Syntax_isNatLit_x3f(v_s_3879_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
return v___x_3881_;
}
else
{
lean_object* v_val_3882_; 
v_val_3882_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v___x_3880_, 1);
return v_val_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_TSyntax_getNat(v_s_3883_);
lean_dec(v_s_3883_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3888_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3890_ = l_Lean_Syntax_isLit_x3f(v___x_3889_, v_stx_3888_);
if (lean_obj_tag(v___x_3890_) == 1)
{
lean_object* v_val_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_val_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3891_, v___x_3892_, v___x_3892_);
lean_dec(v_val_3891_);
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; 
lean_dec(v___x_3890_);
v___x_3894_ = lean_box(0);
return v___x_3894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3895_);
lean_dec(v_stx_3895_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3897_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_unsigned_to_nat(0u);
return v___x_3899_;
}
else
{
lean_object* v_val_3900_; 
v_val_3900_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_val_3900_);
lean_dec_ref_known(v___x_3898_, 1);
return v_val_3900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_TSyntax_getHexNumVal(v_s_3901_);
lean_dec(v_s_3901_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3903_, lean_object* v_p_3904_, lean_object* v_n_3905_){
_start:
{
uint8_t v___x_3906_; 
v___x_3906_ = lean_string_utf8_at_end(v_s_3903_, v_p_3904_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; uint32_t v___x_3908_; uint32_t v___x_3909_; uint8_t v___x_3910_; 
v___x_3907_ = lean_string_utf8_next(v_s_3903_, v_p_3904_);
v___x_3908_ = lean_string_utf8_get(v_s_3903_, v_p_3904_);
lean_dec(v_p_3904_);
v___x_3909_ = 95;
v___x_3910_ = lean_uint32_dec_eq(v___x_3908_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = lean_nat_add(v_n_3905_, v___x_3911_);
lean_dec(v_n_3905_);
v_p_3904_ = v___x_3907_;
v_n_3905_ = v___x_3912_;
goto _start;
}
else
{
v_p_3904_ = v___x_3907_;
goto _start;
}
}
else
{
lean_dec(v_p_3904_);
return v_n_3905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3915_, lean_object* v_p_3916_, lean_object* v_n_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3915_, v_p_3916_, v_n_3917_);
lean_dec_ref(v_s_3915_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3919_){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3921_ = l_Lean_Syntax_isLit_x3f(v___x_3920_, v_s_3919_);
if (lean_obj_tag(v___x_3921_) == 1)
{
lean_object* v_val_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_val_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_val_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = lean_unsigned_to_nat(0u);
v___x_3924_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3922_, v___x_3923_, v___x_3923_);
lean_dec(v_val_3922_);
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; 
lean_dec(v___x_3921_);
v___x_3925_ = lean_unsigned_to_nat(0u);
return v___x_3925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_TSyntax_getHexNumSize(v_s_3926_);
lean_dec(v_s_3926_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_Syntax_getId(v_s_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_TSyntax_getId(v_s_3930_);
lean_dec(v_s_3930_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3939_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; 
v___x_3941_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_TSyntax_getScientific(v_s_3943_);
lean_dec(v_s_3943_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_Syntax_isStrLit_x3f(v_s_3945_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3947_;
}
else
{
lean_object* v_val_3948_; 
v_val_3948_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_val_3948_);
lean_dec_ref_known(v___x_3946_, 1);
return v_val_3948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_TSyntax_getString(v_s_3949_);
lean_dec(v_s_3949_);
return v_res_3950_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_Syntax_isCharLit_x3f(v_s_3951_);
if (lean_obj_tag(v___x_3952_) == 0)
{
uint32_t v___x_3953_; 
v___x_3953_ = 65;
return v___x_3953_;
}
else
{
lean_object* v_val_3954_; uint32_t v___x_3955_; 
v_val_3954_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_val_3954_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3955_ = lean_unbox_uint32(v_val_3954_);
lean_dec(v_val_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3956_){
_start:
{
uint32_t v_res_3957_; lean_object* v_r_3958_; 
v_res_3957_ = l_Lean_TSyntax_getChar(v_s_3956_);
lean_dec(v_s_3956_);
v_r_3958_ = lean_box_uint32(v_res_3957_);
return v_r_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3959_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Syntax_isNameLit_x3f(v_s_3959_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_box(0);
return v___x_3961_;
}
else
{
lean_object* v_val_3962_; 
v_val_3962_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_val_3962_);
lean_dec_ref_known(v___x_3960_, 1);
return v_val_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_TSyntax_getName(v_s_3963_);
lean_dec(v_s_3963_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3965_){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = l_Lean_Syntax_getArg(v_s_3965_, v___x_3966_);
v___x_3968_ = l_Lean_Syntax_getId(v___x_3967_);
lean_dec(v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_TSyntax_getHygieneInfo(v_s_3969_);
lean_dec(v_s_3969_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3971_, v_a_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3974_, v_a_3975_);
lean_dec_ref(v_a_3975_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3977_){
_start:
{
lean_object* v___f_3978_; 
v___f_3978_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3978_, 0, v_sep_3977_);
return v___f_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3979_, lean_object* v_sep_3980_){
_start:
{
lean_object* v___f_3981_; 
v___f_3981_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3981_, 0, v_sep_3980_);
return v___f_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3982_, lean_object* v_sep_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3982_, v_sep_3983_);
lean_dec(v_k_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3985_, lean_object* v_val_3986_, uint8_t v_canonical_3987_){
_start:
{
lean_object* v___x_3988_; lean_object* v_src_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v_imported_3992_; lean_object* v_ctx_3993_; lean_object* v_scopes_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4010_; 
v___x_3988_ = lean_unsigned_to_nat(0u);
v_src_3989_ = l_Lean_Syntax_getArg(v_s_3985_, v___x_3988_);
v___x_3990_ = l_Lean_Syntax_getId(v_src_3989_);
v___x_3991_ = l_Lean_extractMacroScopes(v___x_3990_);
v_imported_3992_ = lean_ctor_get(v___x_3991_, 1);
v_ctx_3993_ = lean_ctor_get(v___x_3991_, 2);
v_scopes_3994_ = lean_ctor_get(v___x_3991_, 3);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4010_ == 0)
{
lean_object* v_unused_4011_; 
v_unused_4011_ = lean_ctor_get(v___x_3991_, 0);
lean_dec(v_unused_4011_);
v___x_3996_ = v___x_3991_;
v_isShared_3997_ = v_isSharedCheck_4010_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_scopes_3994_);
lean_inc(v_ctx_3993_);
lean_inc(v_imported_3992_);
lean_dec(v___x_3991_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4010_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3998_; lean_object* v___x_4000_; 
v___x_3998_ = l_Lean_Name_eraseMacroScopes(v_val_3986_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_3998_);
v___x_4000_ = v___x_3996_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_imported_3992_);
lean_ctor_set(v_reuseFailAlloc_4009_, 2, v_ctx_3993_);
lean_ctor_set(v_reuseFailAlloc_4009_, 3, v_scopes_3994_);
v___x_4000_ = v_reuseFailAlloc_4009_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
lean_object* v_id_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_id_4001_ = l_Lean_MacroScopesView_review(v___x_4000_);
v___x_4002_ = l_Lean_SourceInfo_fromRef(v_src_3989_, v_canonical_3987_);
lean_dec(v_src_3989_);
v___x_4003_ = 1;
v___x_4004_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3986_, v___x_4003_);
v___x_4005_ = lean_string_utf8_byte_size(v___x_4004_);
v___x_4006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4004_);
lean_ctor_set(v___x_4006_, 1, v___x_3988_);
lean_ctor_set(v___x_4006_, 2, v___x_4005_);
v___x_4007_ = lean_box(0);
v___x_4008_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4002_);
lean_ctor_set(v___x_4008_, 1, v___x_4006_);
lean_ctor_set(v___x_4008_, 2, v_id_4001_);
lean_ctor_set(v___x_4008_, 3, v___x_4007_);
return v___x_4008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4012_, lean_object* v_val_4013_, lean_object* v_canonical_4014_){
_start:
{
uint8_t v_canonical_boxed_4015_; lean_object* v_res_4016_; 
v_canonical_boxed_4015_ = lean_unbox(v_canonical_4014_);
v_res_4016_ = l_Lean_HygieneInfo_mkIdent(v_s_4012_, v_val_4013_, v_canonical_boxed_4015_);
lean_dec(v_s_4012_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4017_, lean_object* v_inst_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_apply_1(v_inst_4017_, v_a_4019_);
v___x_4021_ = lean_apply_1(v_inst_4018_, v___x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4022_, lean_object* v_inst_4023_){
_start:
{
lean_object* v___f_4024_; 
v___f_4024_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4024_, 0, v_inst_4022_);
lean_closure_set(v___f_4024_, 1, v_inst_4023_);
return v___f_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4025_, lean_object* v_k_4026_, lean_object* v_k_x27_4027_, lean_object* v_inst_4028_, lean_object* v_inst_4029_){
_start:
{
lean_object* v___f_4030_; 
v___f_4030_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4030_, 0, v_inst_4028_);
lean_closure_set(v___f_4030_, 1, v_inst_4029_);
return v___f_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4031_, lean_object* v_k_4032_, lean_object* v_k_x27_4033_, lean_object* v_inst_4034_, lean_object* v_inst_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4031_, v_k_4032_, v_k_x27_4033_, v_inst_4034_, v_inst_4035_);
lean_dec(v_k_x27_4033_);
lean_dec(v_k_4032_);
return v_res_4036_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4045_ = l_Lean_mkCIdent(v___x_4044_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4051_ = l_Lean_mkCIdent(v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4052_){
_start:
{
if (v_x_4052_ == 0)
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4053_;
}
else
{
lean_object* v___x_4054_; 
v___x_4054_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4055_){
_start:
{
uint8_t v_x_85__boxed_4056_; lean_object* v_res_4057_; 
v_x_85__boxed_4056_ = lean_unbox(v_x_4055_);
v_res_4057_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4056_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4060_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_box(2);
v___x_4062_ = l_Lean_Syntax_mkCharLit(v_val_4060_, v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4063_){
_start:
{
uint32_t v_val_boxed_4064_; lean_object* v_res_4065_; 
v_val_boxed_4064_ = lean_unbox_uint32(v_val_4063_);
lean_dec(v_val_4063_);
v_res_4065_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4064_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4068_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = lean_box(2);
v___x_4070_ = l_Lean_Syntax_mkStrLit(v_val_4068_, v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4073_){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = l_Nat_reprFast(v_n_4073_);
v___x_4075_ = lean_box(2);
v___x_4076_ = l_Lean_Syntax_mkNumLit(v___x_4074_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4084_){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4085_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4086_ = lean_substring_tostring(v_s_4084_);
v___x_4087_ = lean_box(2);
v___x_4088_ = l_Lean_Syntax_mkStrLit(v___x_4086_, v___x_4087_);
v___x_4089_ = lean_unsigned_to_nat(1u);
v___x_4090_ = lean_mk_empty_array_with_capacity(v___x_4089_);
v___x_4091_ = lean_array_push(v___x_4090_, v___x_4088_);
v___x_4092_ = l_Lean_Syntax_mkCApp(v___x_4085_, v___x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4095_, lean_object* v_x_4096_){
_start:
{
switch(lean_obj_tag(v_x_4096_))
{
case 0:
{
uint8_t v___x_4097_; 
v___x_4097_ = l_List_isEmpty___redArg(v_acc_4095_);
if (v___x_4097_ == 0)
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_acc_4095_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; 
lean_dec(v_acc_4095_);
v___x_4099_ = lean_box(0);
return v___x_4099_;
}
}
case 1:
{
lean_object* v_pre_4100_; lean_object* v_str_4101_; lean_object* v_val_4103_; lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v_pre_4100_ = lean_ctor_get(v_x_4096_, 0);
lean_inc(v_pre_4100_);
v_str_4101_ = lean_ctor_get(v_x_4096_, 1);
lean_inc_ref(v_str_4101_);
lean_dec_ref_known(v_x_4096_, 2);
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = lean_string_utf8_byte_size(v_str_4101_);
v___x_4108_ = lean_nat_dec_lt(v___x_4106_, v___x_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4109_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4110_ = lean_string_append(v___x_4109_, v_str_4101_);
lean_dec_ref(v_str_4101_);
v___x_4111_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4112_ = lean_string_append(v___x_4110_, v___x_4111_);
v_val_4103_ = v___x_4112_;
goto v___jp_4102_;
}
else
{
lean_object* v___f_4113_; uint8_t v___y_4115_; lean_object* v___f_4122_; uint32_t v___y_4129_; uint32_t v___y_4134_; uint8_t v___y_4135_; uint8_t v_c_4149_; uint8_t v___x_4158_; uint8_t v___x_4159_; 
v___f_4113_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4122_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4149_ = lean_string_get_byte_fast(v_str_4101_, v___x_4106_);
v___x_4158_ = 97;
v___x_4159_ = lean_uint8_dec_le(v___x_4158_, v_c_4149_);
if (v___x_4159_ == 0)
{
goto v___jp_4153_;
}
else
{
uint8_t v___x_4160_; uint8_t v___x_4161_; 
v___x_4160_ = 122;
v___x_4161_ = lean_uint8_dec_le(v_c_4149_, v___x_4160_);
if (v___x_4161_ == 0)
{
goto v___jp_4153_;
}
else
{
goto v___jp_4146_;
}
}
v___jp_4114_:
{
if (v___y_4115_ == 0)
{
uint8_t v___x_4116_; 
lean_inc_ref(v_str_4101_);
v___x_4116_ = lean_string_any(v_str_4101_, v___f_4113_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4117_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4118_ = lean_string_append(v___x_4117_, v_str_4101_);
lean_dec_ref(v_str_4101_);
v___x_4119_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4120_ = lean_string_append(v___x_4118_, v___x_4119_);
v_val_4103_ = v___x_4120_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4121_; 
lean_dec_ref(v_str_4101_);
lean_dec(v_pre_4100_);
lean_dec(v_acc_4095_);
v___x_4121_ = lean_box(0);
return v___x_4121_;
}
}
else
{
v_val_4103_ = v_str_4101_;
goto v___jp_4102_;
}
}
v___jp_4123_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; 
lean_inc_ref(v_str_4101_);
v___x_4124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4124_, 0, v_str_4101_);
lean_ctor_set(v___x_4124_, 1, v___x_4106_);
lean_ctor_set(v___x_4124_, 2, v___x_4107_);
v___x_4125_ = lean_unsigned_to_nat(1u);
v___x_4126_ = lean_substring_drop(v___x_4124_, v___x_4125_);
v___x_4127_ = lean_substring_all(v___x_4126_, v___f_4122_);
v___y_4115_ = v___x_4127_;
goto v___jp_4114_;
}
v___jp_4128_:
{
uint32_t v___x_4130_; uint8_t v___x_4131_; 
v___x_4130_ = 95;
v___x_4131_ = lean_uint32_dec_eq(v___y_4129_, v___x_4130_);
if (v___x_4131_ == 0)
{
uint8_t v___x_4132_; 
v___x_4132_ = l_Lean_isLetterLike(v___y_4129_);
if (v___x_4132_ == 0)
{
v___y_4115_ = v___x_4132_;
goto v___jp_4114_;
}
else
{
goto v___jp_4123_;
}
}
else
{
goto v___jp_4123_;
}
}
v___jp_4133_:
{
if (v___y_4135_ == 0)
{
uint32_t v___x_4136_; uint8_t v___x_4137_; 
v___x_4136_ = 97;
v___x_4137_ = lean_uint32_dec_le(v___x_4136_, v___y_4134_);
if (v___x_4137_ == 0)
{
v___y_4129_ = v___y_4134_;
goto v___jp_4128_;
}
else
{
uint32_t v___x_4138_; uint8_t v___x_4139_; 
v___x_4138_ = 122;
v___x_4139_ = lean_uint32_dec_le(v___y_4134_, v___x_4138_);
if (v___x_4139_ == 0)
{
v___y_4129_ = v___y_4134_;
goto v___jp_4128_;
}
else
{
goto v___jp_4123_;
}
}
}
else
{
goto v___jp_4123_;
}
}
v___jp_4140_:
{
uint32_t v___x_4141_; uint32_t v___x_4142_; uint8_t v___x_4143_; 
v___x_4141_ = lean_string_utf8_get(v_str_4101_, v___x_4106_);
v___x_4142_ = 65;
v___x_4143_ = lean_uint32_dec_le(v___x_4142_, v___x_4141_);
if (v___x_4143_ == 0)
{
v___y_4134_ = v___x_4141_;
v___y_4135_ = v___x_4143_;
goto v___jp_4133_;
}
else
{
uint32_t v___x_4144_; uint8_t v___x_4145_; 
v___x_4144_ = 90;
v___x_4145_ = lean_uint32_dec_le(v___x_4141_, v___x_4144_);
v___y_4134_ = v___x_4141_;
v___y_4135_ = v___x_4145_;
goto v___jp_4133_;
}
}
v___jp_4146_:
{
lean_object* v___x_4147_; uint8_t v___x_4148_; 
v___x_4147_ = lean_unsigned_to_nat(1u);
v___x_4148_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4101_, v___x_4147_);
if (v___x_4148_ == 0)
{
goto v___jp_4140_;
}
else
{
v___y_4115_ = v___x_4148_;
goto v___jp_4114_;
}
}
v___jp_4150_:
{
uint8_t v___x_4151_; uint8_t v___x_4152_; 
v___x_4151_ = 95;
v___x_4152_ = lean_uint8_dec_eq(v_c_4149_, v___x_4151_);
if (v___x_4152_ == 0)
{
goto v___jp_4140_;
}
else
{
goto v___jp_4146_;
}
}
v___jp_4153_:
{
uint8_t v___x_4154_; uint8_t v___x_4155_; 
v___x_4154_ = 65;
v___x_4155_ = lean_uint8_dec_le(v___x_4154_, v_c_4149_);
if (v___x_4155_ == 0)
{
goto v___jp_4150_;
}
else
{
uint8_t v___x_4156_; uint8_t v___x_4157_; 
v___x_4156_ = 90;
v___x_4157_ = lean_uint8_dec_le(v_c_4149_, v___x_4156_);
if (v___x_4157_ == 0)
{
goto v___jp_4150_;
}
else
{
goto v___jp_4146_;
}
}
}
}
v___jp_4102_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4104_, 0, v_val_4103_);
lean_ctor_set(v___x_4104_, 1, v_acc_4095_);
v_acc_4095_ = v___x_4104_;
v_x_4096_ = v_pre_4100_;
goto _start;
}
}
default: 
{
lean_object* v___x_4162_; 
lean_dec_ref_known(v_x_4096_, 2);
lean_dec(v_acc_4095_);
v___x_4162_ = lean_box(0);
return v___x_4162_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4170_ = l_Lean_mkCIdent(v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4181_){
_start:
{
switch(lean_obj_tag(v_x_4181_))
{
case 0:
{
lean_object* v___x_4182_; 
v___x_4182_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4182_;
}
case 1:
{
lean_object* v_pre_4183_; lean_object* v_str_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v_pre_4183_ = lean_ctor_get(v_x_4181_, 0);
lean_inc(v_pre_4183_);
v_str_4184_ = lean_ctor_get(v_x_4181_, 1);
lean_inc_ref(v_str_4184_);
lean_dec_ref_known(v_x_4181_, 2);
v___x_4185_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4186_ = l_Lean_quoteNameMk(v_pre_4183_);
v___x_4187_ = lean_box(2);
v___x_4188_ = l_Lean_Syntax_mkStrLit(v_str_4184_, v___x_4187_);
v___x_4189_ = lean_unsigned_to_nat(2u);
v___x_4190_ = lean_mk_empty_array_with_capacity(v___x_4189_);
v___x_4191_ = lean_array_push(v___x_4190_, v___x_4186_);
v___x_4192_ = lean_array_push(v___x_4191_, v___x_4188_);
v___x_4193_ = l_Lean_Syntax_mkCApp(v___x_4185_, v___x_4192_);
return v___x_4193_;
}
default: 
{
lean_object* v_pre_4194_; lean_object* v_i_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_pre_4194_ = lean_ctor_get(v_x_4181_, 0);
lean_inc(v_pre_4194_);
v_i_4195_ = lean_ctor_get(v_x_4181_, 1);
lean_inc(v_i_4195_);
lean_dec_ref_known(v_x_4181_, 2);
v___x_4196_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4197_ = l_Lean_quoteNameMk(v_pre_4194_);
v___x_4198_ = l_Nat_reprFast(v_i_4195_);
v___x_4199_ = lean_box(2);
v___x_4200_ = l_Lean_Syntax_mkNumLit(v___x_4198_, v___x_4199_);
v___x_4201_ = lean_unsigned_to_nat(2u);
v___x_4202_ = lean_mk_empty_array_with_capacity(v___x_4201_);
v___x_4203_ = lean_array_push(v___x_4202_, v___x_4197_);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4200_);
v___x_4205_ = l_Lean_Syntax_mkCApp(v___x_4196_, v___x_4204_);
return v___x_4205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4212_){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_box(0);
lean_inc(v_n_4212_);
v___x_4214_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4213_, v_n_4212_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_quoteNameMk(v_n_4212_);
return v___x_4215_;
}
else
{
lean_object* v_val_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_dec(v_n_4212_);
v_val_4216_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_val_4216_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4217_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4218_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4219_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4220_ = lean_string_intercalate(v___x_4219_, v_val_4216_);
v___x_4221_ = lean_string_append(v___x_4218_, v___x_4220_);
lean_dec_ref(v___x_4220_);
v___x_4222_ = lean_box(2);
v___x_4223_ = l_Lean_Syntax_mkNameLit(v___x_4221_, v___x_4222_);
v___x_4224_ = lean_unsigned_to_nat(1u);
v___x_4225_ = lean_mk_empty_array_with_capacity(v___x_4224_);
v___x_4226_ = lean_array_push(v___x_4225_, v___x_4223_);
v___x_4227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4222_);
lean_ctor_set(v___x_4227_, 1, v___x_4217_);
lean_ctor_set(v___x_4227_, 2, v___x_4226_);
return v___x_4227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4228_){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = lean_box(0);
lean_inc(v_n_4228_);
v___x_4230_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4229_, v_n_4228_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_quoteNameMk(v_n_4228_);
return v___x_4231_;
}
else
{
lean_object* v_val_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
lean_dec(v_n_4228_);
v_val_4232_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_val_4232_);
lean_dec_ref_known(v___x_4230_, 1);
v___x_4233_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4234_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4235_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4236_ = lean_string_intercalate(v___x_4235_, v_val_4232_);
v___x_4237_ = lean_string_append(v___x_4234_, v___x_4236_);
lean_dec_ref(v___x_4236_);
v___x_4238_ = lean_box(2);
v___x_4239_ = l_Lean_Syntax_mkNameLit(v___x_4237_, v___x_4238_);
v___x_4240_ = lean_unsigned_to_nat(1u);
v___x_4241_ = lean_mk_empty_array_with_capacity(v___x_4240_);
v___x_4242_ = lean_array_push(v___x_4241_, v___x_4239_);
v___x_4243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4238_);
lean_ctor_set(v___x_4243_, 1, v___x_4233_);
lean_ctor_set(v___x_4243_, 2, v___x_4242_);
return v___x_4243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4251_, lean_object* v_inst_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v_fst_4254_; lean_object* v_snd_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v_fst_4254_ = lean_ctor_get(v_x_4253_, 0);
lean_inc(v_fst_4254_);
v_snd_4255_ = lean_ctor_get(v_x_4253_, 1);
lean_inc(v_snd_4255_);
lean_dec_ref(v_x_4253_);
v___x_4256_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4257_ = lean_apply_1(v_inst_4251_, v_fst_4254_);
v___x_4258_ = lean_apply_1(v_inst_4252_, v_snd_4255_);
v___x_4259_ = lean_unsigned_to_nat(2u);
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4259_);
v___x_4261_ = lean_array_push(v___x_4260_, v___x_4257_);
v___x_4262_ = lean_array_push(v___x_4261_, v___x_4258_);
v___x_4263_ = l_Lean_Syntax_mkCApp(v___x_4256_, v___x_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4264_, lean_object* v_inst_4265_){
_start:
{
lean_object* v___f_4266_; 
v___f_4266_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4266_, 0, v_inst_4264_);
lean_closure_set(v___f_4266_, 1, v_inst_4265_);
return v___f_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4267_, lean_object* v_00_u03b2_4268_, lean_object* v_inst_4269_, lean_object* v_inst_4270_){
_start:
{
lean_object* v___f_4271_; 
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4271_, 0, v_inst_4269_);
lean_closure_set(v___f_4271_, 1, v_inst_4270_);
return v___f_4271_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4278_ = l_Lean_mkCIdent(v___x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4283_, lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4284_) == 0)
{
lean_object* v___x_4285_; 
lean_dec_ref(v_inst_4283_);
v___x_4285_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4285_;
}
else
{
lean_object* v_head_4286_; lean_object* v_tail_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_head_4286_ = lean_ctor_get(v_x_4284_, 0);
lean_inc(v_head_4286_);
v_tail_4287_ = lean_ctor_get(v_x_4284_, 1);
lean_inc(v_tail_4287_);
lean_dec_ref_known(v_x_4284_, 2);
v___x_4288_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4283_);
v___x_4289_ = lean_apply_1(v_inst_4283_, v_head_4286_);
v___x_4290_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4283_, v_tail_4287_);
v___x_4291_ = lean_unsigned_to_nat(2u);
v___x_4292_ = lean_mk_empty_array_with_capacity(v___x_4291_);
v___x_4293_ = lean_array_push(v___x_4292_, v___x_4289_);
v___x_4294_ = lean_array_push(v___x_4293_, v___x_4290_);
v___x_4295_ = l_Lean_Syntax_mkCApp(v___x_4288_, v___x_4294_);
return v___x_4295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4296_, lean_object* v_inst_4297_, lean_object* v_x_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4297_, v_x_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4300_, v_a_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4303_, lean_object* v_inst_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4304_, v_a_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4308_, 0, lean_box(0));
lean_closure_set(v___x_4308_, 1, v_inst_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4309_, lean_object* v_inst_4310_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4311_, 0, lean_box(0));
lean_closure_set(v___x_4311_, 1, v_inst_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4314_, lean_object* v_xs_4315_, lean_object* v_i_4316_, lean_object* v_args_4317_){
_start:
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = lean_array_get_size(v_xs_4315_);
v___x_4319_ = lean_nat_dec_lt(v_i_4316_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
lean_dec(v_i_4316_);
lean_dec_ref(v_inst_4314_);
v___x_4320_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4321_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4322_ = l_Nat_reprFast(v___x_4318_);
v___x_4323_ = lean_string_append(v___x_4321_, v___x_4322_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = l_Lean_Name_mkStr2(v___x_4320_, v___x_4323_);
v___x_4325_ = l_Lean_Syntax_mkCApp(v___x_4324_, v_args_4317_);
return v___x_4325_;
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4326_ = lean_unsigned_to_nat(1u);
v___x_4327_ = lean_nat_add(v_i_4316_, v___x_4326_);
v___x_4328_ = lean_array_fget_borrowed(v_xs_4315_, v_i_4316_);
lean_dec(v_i_4316_);
lean_inc_ref(v_inst_4314_);
lean_inc(v___x_4328_);
v___x_4329_ = lean_apply_1(v_inst_4314_, v___x_4328_);
v___x_4330_ = lean_array_push(v_args_4317_, v___x_4329_);
v_i_4316_ = v___x_4327_;
v_args_4317_ = v___x_4330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4332_, lean_object* v_xs_4333_, lean_object* v_i_4334_, lean_object* v_args_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4332_, v_xs_4333_, v_i_4334_, v_args_4335_);
lean_dec_ref(v_xs_4333_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4337_, lean_object* v_inst_4338_, lean_object* v_xs_4339_, lean_object* v_i_4340_, lean_object* v_args_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4338_, v_xs_4339_, v_i_4340_, v_args_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4343_, lean_object* v_inst_4344_, lean_object* v_xs_4345_, lean_object* v_i_4346_, lean_object* v_args_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4343_, v_inst_4344_, v_xs_4345_, v_i_4346_, v_args_4347_);
lean_dec_ref(v_xs_4345_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4353_, lean_object* v_xs_4354_){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4355_ = lean_array_get_size(v_xs_4354_);
v___x_4356_ = lean_unsigned_to_nat(8u);
v___x_4357_ = lean_nat_dec_le(v___x_4355_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4358_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4359_ = lean_array_to_list(v_xs_4354_);
v___x_4360_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4353_, v___x_4359_);
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = lean_mk_empty_array_with_capacity(v___x_4361_);
v___x_4363_ = lean_array_push(v___x_4362_, v___x_4360_);
v___x_4364_ = l_Lean_Syntax_mkCApp(v___x_4358_, v___x_4363_);
return v___x_4364_;
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4367_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4353_, v_xs_4354_, v___x_4365_, v___x_4366_);
lean_dec_ref(v_xs_4354_);
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4368_, lean_object* v_inst_4369_, lean_object* v_xs_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4369_, v_xs_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4372_, lean_object* v_xs_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4372_, v_xs_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4375_, lean_object* v_inst_4376_, lean_object* v_xs_4377_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4376_, v_xs_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4380_, 0, lean_box(0));
lean_closure_set(v___x_4380_, 1, v_inst_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4381_, lean_object* v_inst_4382_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4383_, 0, lean_box(0));
lean_closure_set(v___x_4383_, 1, v_inst_4382_);
return v___x_4383_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4390_ = l_Lean_mkIdent(v___x_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4395_, lean_object* v_x_4396_){
_start:
{
if (lean_obj_tag(v_x_4396_) == 0)
{
lean_object* v___x_4397_; 
lean_dec_ref(v_inst_4395_);
v___x_4397_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4397_;
}
else
{
lean_object* v_val_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v_val_4398_ = lean_ctor_get(v_x_4396_, 0);
lean_inc(v_val_4398_);
lean_dec_ref_known(v_x_4396_, 1);
v___x_4399_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4400_ = lean_apply_1(v_inst_4395_, v_val_4398_);
v___x_4401_ = lean_unsigned_to_nat(1u);
v___x_4402_ = lean_mk_empty_array_with_capacity(v___x_4401_);
v___x_4403_ = lean_array_push(v___x_4402_, v___x_4400_);
v___x_4404_ = l_Lean_Syntax_mkCApp(v___x_4399_, v___x_4403_);
return v___x_4404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4405_){
_start:
{
lean_object* v___f_4406_; 
v___f_4406_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4406_, 0, v_inst_4405_);
return v___f_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4407_, lean_object* v_inst_4408_){
_start:
{
lean_object* v___f_4409_; 
v___f_4409_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4409_, 0, v_inst_4408_);
return v___f_4409_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4410_, lean_object* v_k_4411_){
_start:
{
lean_object* v___x_4412_; uint8_t v___x_4413_; 
v___x_4412_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4413_ = lean_name_eq(v_k_4411_, v___x_4412_);
if (v___x_4413_ == 0)
{
uint8_t v___x_4414_; 
v___x_4414_ = 1;
return v___x_4414_;
}
else
{
return v___x_4410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4415_, lean_object* v_k_4416_){
_start:
{
uint8_t v___x_442__boxed_4417_; uint8_t v_res_4418_; lean_object* v_r_4419_; 
v___x_442__boxed_4417_ = lean_unbox(v___x_4415_);
v_res_4418_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4417_, v_k_4416_);
lean_dec(v_k_4416_);
v_r_4419_ = lean_box(v_res_4418_);
return v_r_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_methods_4424_; lean_object* v_quotContext_4425_; lean_object* v_currMacroScope_4426_; lean_object* v_currRecDepth_4427_; lean_object* v_maxRecDepth_4428_; lean_object* v_ref_4429_; uint8_t v___x_4430_; 
v_methods_4424_ = lean_ctor_get(v_a_4422_, 0);
v_quotContext_4425_ = lean_ctor_get(v_a_4422_, 1);
v_currMacroScope_4426_ = lean_ctor_get(v_a_4422_, 2);
v_currRecDepth_4427_ = lean_ctor_get(v_a_4422_, 3);
v_maxRecDepth_4428_ = lean_ctor_get(v_a_4422_, 4);
v_ref_4429_ = lean_ctor_get(v_a_4422_, 5);
v___x_4430_ = lean_nat_dec_eq(v_currRecDepth_4427_, v_maxRecDepth_4428_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; lean_object* v___f_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4431_ = lean_box(v___x_4430_);
v___f_4432_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4432_, 0, v___x_4431_);
v___x_4433_ = lean_unsigned_to_nat(1u);
v___x_4434_ = lean_nat_add(v_currRecDepth_4427_, v___x_4433_);
lean_inc(v_ref_4429_);
lean_inc(v_maxRecDepth_4428_);
lean_inc(v_currMacroScope_4426_);
lean_inc(v_quotContext_4425_);
lean_inc(v_methods_4424_);
v___x_4435_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4435_, 0, v_methods_4424_);
lean_ctor_set(v___x_4435_, 1, v_quotContext_4425_);
lean_ctor_set(v___x_4435_, 2, v_currMacroScope_4426_);
lean_ctor_set(v___x_4435_, 3, v___x_4434_);
lean_ctor_set(v___x_4435_, 4, v_maxRecDepth_4428_);
lean_ctor_set(v___x_4435_, 5, v_ref_4429_);
lean_inc_ref(v___x_4435_);
v___x_4436_ = l_Lean_expandMacros(v_stx_4421_, v___f_4432_, v___x_4435_, v_a_4423_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4450_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_a_4438_ = lean_ctor_get(v___x_4436_, 1);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4440_ = v___x_4436_;
v_isShared_4441_ = v_isSharedCheck_4450_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4450_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; uint8_t v___x_4443_; 
v___x_4442_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4437_);
v___x_4443_ = l_Lean_Syntax_isOfKind(v_a_4437_, v___x_4442_);
if (v___x_4443_ == 0)
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
lean_del_object(v___x_4440_);
v___x_4444_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4445_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4437_, v___x_4444_, v___x_4435_, v_a_4438_);
lean_dec_ref_known(v___x_4435_, 6);
lean_dec(v_a_4437_);
return v___x_4445_;
}
else
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
lean_dec_ref_known(v___x_4435_, 6);
v___x_4446_ = l_Lean_TSyntax_getNat(v_a_4437_);
lean_dec(v_a_4437_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4446_);
v___x_4448_ = v___x_4440_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
lean_ctor_set(v_reuseFailAlloc_4449_, 1, v_a_4438_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref_known(v___x_4435_, 6);
v_a_4451_ = lean_ctor_get(v___x_4436_, 0);
v_a_4452_ = lean_ctor_get(v___x_4436_, 1);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4436_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_inc(v_a_4451_);
lean_dec(v___x_4436_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4451_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4460_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v_stx_4421_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
lean_ctor_set(v___x_4462_, 1, v_a_4423_);
return v___x_4462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_evalPrec(v_stx_4463_, v_a_4464_, v_a_4465_);
lean_dec_ref(v_a_4464_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_methods_4471_; lean_object* v_quotContext_4472_; lean_object* v_currMacroScope_4473_; lean_object* v_currRecDepth_4474_; lean_object* v_maxRecDepth_4475_; lean_object* v_ref_4476_; uint8_t v___x_4477_; 
v_methods_4471_ = lean_ctor_get(v_a_4469_, 0);
v_quotContext_4472_ = lean_ctor_get(v_a_4469_, 1);
v_currMacroScope_4473_ = lean_ctor_get(v_a_4469_, 2);
v_currRecDepth_4474_ = lean_ctor_get(v_a_4469_, 3);
v_maxRecDepth_4475_ = lean_ctor_get(v_a_4469_, 4);
v_ref_4476_ = lean_ctor_get(v_a_4469_, 5);
v___x_4477_ = lean_nat_dec_eq(v_currRecDepth_4474_, v_maxRecDepth_4475_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; lean_object* v___f_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4478_ = lean_box(v___x_4477_);
v___f_4479_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4479_, 0, v___x_4478_);
v___x_4480_ = lean_unsigned_to_nat(1u);
v___x_4481_ = lean_nat_add(v_currRecDepth_4474_, v___x_4480_);
lean_inc(v_ref_4476_);
lean_inc(v_maxRecDepth_4475_);
lean_inc(v_currMacroScope_4473_);
lean_inc(v_quotContext_4472_);
lean_inc(v_methods_4471_);
v___x_4482_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4482_, 0, v_methods_4471_);
lean_ctor_set(v___x_4482_, 1, v_quotContext_4472_);
lean_ctor_set(v___x_4482_, 2, v_currMacroScope_4473_);
lean_ctor_set(v___x_4482_, 3, v___x_4481_);
lean_ctor_set(v___x_4482_, 4, v_maxRecDepth_4475_);
lean_ctor_set(v___x_4482_, 5, v_ref_4476_);
lean_inc_ref(v___x_4482_);
v___x_4483_ = l_Lean_expandMacros(v_stx_4468_, v___f_4479_, v___x_4482_, v_a_4470_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4497_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
v_a_4485_ = lean_ctor_get(v___x_4483_, 1);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4487_ = v___x_4483_;
v_isShared_4488_ = v_isSharedCheck_4497_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_inc(v_a_4484_);
lean_dec(v___x_4483_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4497_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4489_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4484_);
v___x_4490_ = l_Lean_Syntax_isOfKind(v_a_4484_, v___x_4489_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
lean_del_object(v___x_4487_);
v___x_4491_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4492_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4484_, v___x_4491_, v___x_4482_, v_a_4485_);
lean_dec_ref_known(v___x_4482_, 6);
lean_dec(v_a_4484_);
return v___x_4492_;
}
else
{
lean_object* v___x_4493_; lean_object* v___x_4495_; 
lean_dec_ref_known(v___x_4482_, 6);
v___x_4493_ = l_Lean_TSyntax_getNat(v_a_4484_);
lean_dec(v_a_4484_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4493_);
v___x_4495_ = v___x_4487_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_a_4485_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref_known(v___x_4482_, 6);
v_a_4498_ = lean_ctor_get(v___x_4483_, 0);
v_a_4499_ = lean_ctor_get(v___x_4483_, 1);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4483_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_inc(v_a_4498_);
lean_dec(v___x_4483_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4498_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4508_, 0, v_stx_4468_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
lean_ctor_set(v___x_4509_, 1, v_a_4470_);
return v___x_4509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l_Lean_evalPrio(v_stx_4510_, v_a_4511_, v_a_4512_);
lean_dec_ref(v_a_4511_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
if (lean_obj_tag(v_x_4514_) == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_unsigned_to_nat(1000u);
v___x_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v_a_4516_);
return v___x_4518_;
}
else
{
lean_object* v_val_4519_; lean_object* v___x_4520_; 
v_val_4519_ = lean_ctor_get(v_x_4514_, 0);
lean_inc(v_val_4519_);
lean_dec_ref_known(v_x_4514_, 1);
v___x_4520_ = l_Lean_evalPrio(v_val_4519_, v_a_4515_, v_a_4516_);
return v___x_4520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_evalOptPrio(v_x_4521_, v_a_4522_, v_a_4523_);
lean_dec_ref(v_a_4522_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4525_, lean_object* v_x1_4526_, lean_object* v_x2_4527_){
_start:
{
lean_object* v_fst_4528_; uint8_t v___x_4529_; 
v_fst_4528_ = lean_ctor_get(v_x1_4526_, 0);
v___x_4529_ = lean_unbox(v_fst_4528_);
if (v___x_4529_ == 0)
{
lean_object* v_snd_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4538_; 
lean_dec(v_x2_4527_);
v_snd_4530_ = lean_ctor_get(v_x1_4526_, 1);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_x1_4526_);
if (v_isSharedCheck_4538_ == 0)
{
lean_object* v_unused_4539_; 
v_unused_4539_ = lean_ctor_get(v_x1_4526_, 0);
lean_dec(v_unused_4539_);
v___x_4532_ = v_x1_4526_;
v_isShared_4533_ = v_isSharedCheck_4538_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_snd_4530_);
lean_dec(v_x1_4526_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4538_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4536_; 
v___x_4534_ = lean_box(v___x_4525_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4534_);
v___x_4536_ = v___x_4532_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_snd_4530_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
else
{
lean_object* v_snd_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4550_; 
v_snd_4540_ = lean_ctor_get(v_x1_4526_, 1);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_x1_4526_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v_x1_4526_, 0);
lean_dec(v_unused_4551_);
v___x_4542_ = v_x1_4526_;
v_isShared_4543_ = v_isSharedCheck_4550_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_snd_4540_);
lean_dec(v_x1_4526_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4550_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
uint8_t v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v___x_4544_ = 0;
v___x_4545_ = lean_array_push(v_snd_4540_, v_x2_4527_);
v___x_4546_ = lean_box(v___x_4544_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 1, v___x_4545_);
lean_ctor_set(v___x_4542_, 0, v___x_4546_);
v___x_4548_ = v___x_4542_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v___x_4545_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4552_, lean_object* v_x1_4553_, lean_object* v_x2_4554_){
_start:
{
uint8_t v___x_87__boxed_4555_; lean_object* v_res_4556_; 
v___x_87__boxed_4555_ = lean_unbox(v___x_4552_);
v_res_4556_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4555_, v_x1_4553_, v_x2_4554_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4578_){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; uint8_t v___x_4583_; 
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4581_ = lean_array_get_size(v_as_4578_);
v___x_4582_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4583_ = lean_nat_dec_lt(v___x_4579_, v___x_4581_);
if (v___x_4583_ == 0)
{
lean_dec_ref(v_as_4578_);
return v___x_4580_;
}
else
{
lean_object* v___x_4584_; lean_object* v___f_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; size_t v___x_4588_; size_t v___x_4589_; lean_object* v___x_4590_; lean_object* v_snd_4591_; 
v___x_4584_ = lean_box(v___x_4583_);
v___f_4585_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4585_, 0, v___x_4584_);
v___x_4586_ = lean_box(v___x_4583_);
v___x_4587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
lean_ctor_set(v___x_4587_, 1, v___x_4580_);
v___x_4588_ = ((size_t)0ULL);
v___x_4589_ = lean_usize_of_nat(v___x_4581_);
v___x_4590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4582_, v___f_4585_, v_as_4578_, v___x_4588_, v___x_4589_, v___x_4587_);
v_snd_4591_ = lean_ctor_get(v___x_4590_, 1);
lean_inc(v_snd_4591_);
lean_dec(v___x_4590_);
return v_snd_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4592_, lean_object* v_as_4593_){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; 
v___x_4594_ = lean_unsigned_to_nat(0u);
v___x_4595_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4596_ = lean_array_get_size(v_as_4593_);
v___x_4597_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4598_ = lean_nat_dec_lt(v___x_4594_, v___x_4596_);
if (v___x_4598_ == 0)
{
lean_dec_ref(v_as_4593_);
return v___x_4595_;
}
else
{
lean_object* v___x_4599_; lean_object* v___f_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; size_t v___x_4603_; size_t v___x_4604_; lean_object* v___x_4605_; lean_object* v_snd_4606_; 
v___x_4599_ = lean_box(v___x_4598_);
v___f_4600_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4600_, 0, v___x_4599_);
v___x_4601_ = lean_box(v___x_4598_);
v___x_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
lean_ctor_set(v___x_4602_, 1, v___x_4595_);
v___x_4603_ = ((size_t)0ULL);
v___x_4604_ = lean_usize_of_nat(v___x_4596_);
v___x_4605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4597_, v___f_4600_, v_as_4593_, v___x_4603_, v___x_4604_, v___x_4602_);
v_snd_4606_ = lean_ctor_get(v___x_4605_, 1);
lean_inc(v_snd_4606_);
lean_dec(v___x_4605_);
return v_snd_4606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4607_, lean_object* v_inst_4608_, lean_object* v_a_4609_, lean_object* v_p_4610_, lean_object* v_acc_4611_, lean_object* v_stx_4612_, uint8_t v_____do__lift_4613_){
_start:
{
if (v_____do__lift_4613_ == 0)
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
lean_dec(v_stx_4612_);
v___x_4622_ = lean_unsigned_to_nat(2u);
v___x_4623_ = lean_nat_add(v_i_4607_, v___x_4622_);
v___x_4624_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4608_, v_a_4609_, v_p_4610_, v___x_4623_, v_acc_4611_);
return v___x_4624_;
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v___x_4625_ = lean_array_get_size(v_acc_4611_);
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = lean_nat_dec_eq(v___x_4625_, v___x_4626_);
if (v___x_4627_ == 0)
{
uint8_t v___x_4628_; 
v___x_4628_ = lean_nat_dec_eq(v_i_4607_, v___x_4626_);
if (v___x_4628_ == 0)
{
goto v___jp_4614_;
}
else
{
if (v___x_4627_ == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4629_ = lean_unsigned_to_nat(2u);
v___x_4630_ = lean_nat_add(v_i_4607_, v___x_4629_);
v___x_4631_ = lean_array_push(v_acc_4611_, v_stx_4612_);
v___x_4632_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4608_, v_a_4609_, v_p_4610_, v___x_4630_, v___x_4631_);
return v___x_4632_;
}
else
{
goto v___jp_4614_;
}
}
}
else
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4633_ = lean_unsigned_to_nat(2u);
v___x_4634_ = lean_nat_add(v_i_4607_, v___x_4633_);
v___x_4635_ = lean_array_push(v_acc_4611_, v_stx_4612_);
v___x_4636_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4608_, v_a_4609_, v_p_4610_, v___x_4634_, v___x_4635_);
return v___x_4636_;
}
}
v___jp_4614_:
{
lean_object* v___x_4615_; lean_object* v_sepStx_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4615_ = lean_nat_pred(v_i_4607_);
v_sepStx_4616_ = lean_array_fget_borrowed(v_a_4609_, v___x_4615_);
lean_dec(v___x_4615_);
v___x_4617_ = lean_unsigned_to_nat(2u);
v___x_4618_ = lean_nat_add(v_i_4607_, v___x_4617_);
lean_inc(v_sepStx_4616_);
v___x_4619_ = lean_array_push(v_acc_4611_, v_sepStx_4616_);
v___x_4620_ = lean_array_push(v___x_4619_, v_stx_4612_);
v___x_4621_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4608_, v_a_4609_, v_p_4610_, v___x_4618_, v___x_4620_);
return v___x_4621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4637_, lean_object* v_inst_4638_, lean_object* v_a_4639_, lean_object* v_p_4640_, lean_object* v_acc_4641_, lean_object* v_stx_4642_, lean_object* v_____do__lift_4643_){
_start:
{
uint8_t v_____do__lift_208__boxed_4644_; lean_object* v_res_4645_; 
v_____do__lift_208__boxed_4644_ = lean_unbox(v_____do__lift_4643_);
v_res_4645_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4637_, v_inst_4638_, v_a_4639_, v_p_4640_, v_acc_4641_, v_stx_4642_, v_____do__lift_208__boxed_4644_);
lean_dec(v_i_4637_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4646_, lean_object* v_a_4647_, lean_object* v_p_4648_, lean_object* v_i_4649_, lean_object* v_acc_4650_){
_start:
{
lean_object* v_toApplicative_4651_; lean_object* v_toBind_4652_; lean_object* v_toPure_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; 
v_toApplicative_4651_ = lean_ctor_get(v_inst_4646_, 0);
v_toBind_4652_ = lean_ctor_get(v_inst_4646_, 1);
lean_inc(v_toBind_4652_);
v_toPure_4653_ = lean_ctor_get(v_toApplicative_4651_, 1);
v___x_4654_ = lean_array_get_size(v_a_4647_);
v___x_4655_ = lean_nat_dec_lt(v_i_4649_, v___x_4654_);
if (v___x_4655_ == 0)
{
lean_object* v___x_4656_; 
lean_inc(v_toPure_4653_);
lean_dec(v_toBind_4652_);
lean_dec(v_i_4649_);
lean_dec(v_p_4648_);
lean_dec_ref(v_a_4647_);
lean_dec_ref(v_inst_4646_);
v___x_4656_ = lean_apply_2(v_toPure_4653_, lean_box(0), v_acc_4650_);
return v___x_4656_;
}
else
{
lean_object* v_stx_4657_; lean_object* v___f_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v_stx_4657_ = lean_array_fget(v_a_4647_, v_i_4649_);
lean_inc(v_stx_4657_);
lean_inc(v_p_4648_);
v___f_4658_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4658_, 0, v_i_4649_);
lean_closure_set(v___f_4658_, 1, v_inst_4646_);
lean_closure_set(v___f_4658_, 2, v_a_4647_);
lean_closure_set(v___f_4658_, 3, v_p_4648_);
lean_closure_set(v___f_4658_, 4, v_acc_4650_);
lean_closure_set(v___f_4658_, 5, v_stx_4657_);
v___x_4659_ = lean_apply_1(v_p_4648_, v_stx_4657_);
v___x_4660_ = lean_apply_4(v_toBind_4652_, lean_box(0), lean_box(0), v___x_4659_, v___f_4658_);
return v___x_4660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4661_, lean_object* v_inst_4662_, lean_object* v_a_4663_, lean_object* v_p_4664_, lean_object* v_i_4665_, lean_object* v_acc_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4662_, v_a_4663_, v_p_4664_, v_i_4665_, v_acc_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4668_, lean_object* v_a_4669_, lean_object* v_p_4670_){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = lean_unsigned_to_nat(0u);
v___x_4672_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4673_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4668_, v_a_4669_, v_p_4670_, v___x_4671_, v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4674_, lean_object* v_inst_4675_, lean_object* v_a_4676_, lean_object* v_p_4677_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Array_filterSepElemsM___redArg(v_inst_4675_, v_a_4676_, v_p_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4679_, lean_object* v_x_4680_){
_start:
{
lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4681_ = lean_apply_1(v_p_4679_, v_x_4680_);
v___x_4682_ = lean_unbox(v___x_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4683_, lean_object* v_x_4684_){
_start:
{
uint8_t v_res_4685_; lean_object* v_r_4686_; 
v_res_4685_ = l_Array_filterSepElems___lam__0(v_p_4683_, v_x_4684_);
v_r_4686_ = lean_box(v_res_4685_);
return v_r_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4687_, lean_object* v_p_4688_, lean_object* v_i_4689_, lean_object* v_acc_4690_){
_start:
{
lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4691_ = lean_array_get_size(v_a_4687_);
v___x_4692_ = lean_nat_dec_lt(v_i_4689_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_dec(v_i_4689_);
lean_dec_ref(v_p_4688_);
return v_acc_4690_;
}
else
{
lean_object* v_stx_4693_; lean_object* v___x_4702_; uint8_t v___x_4703_; 
v_stx_4693_ = lean_array_fget_borrowed(v_a_4687_, v_i_4689_);
lean_inc_ref(v_p_4688_);
lean_inc(v_stx_4693_);
v___x_4702_ = lean_apply_1(v_p_4688_, v_stx_4693_);
v___x_4703_ = lean_unbox(v___x_4702_);
if (v___x_4703_ == 0)
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = lean_unsigned_to_nat(2u);
v___x_4705_ = lean_nat_add(v_i_4689_, v___x_4704_);
lean_dec(v_i_4689_);
v_i_4689_ = v___x_4705_;
goto _start;
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4707_ = lean_array_get_size(v_acc_4690_);
v___x_4708_ = lean_unsigned_to_nat(0u);
v___x_4709_ = lean_nat_dec_eq(v___x_4707_, v___x_4708_);
if (v___x_4709_ == 0)
{
uint8_t v___x_4710_; 
v___x_4710_ = lean_nat_dec_eq(v_i_4689_, v___x_4708_);
if (v___x_4710_ == 0)
{
goto v___jp_4694_;
}
else
{
if (v___x_4709_ == 0)
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4711_ = lean_unsigned_to_nat(2u);
v___x_4712_ = lean_nat_add(v_i_4689_, v___x_4711_);
lean_dec(v_i_4689_);
lean_inc(v_stx_4693_);
v___x_4713_ = lean_array_push(v_acc_4690_, v_stx_4693_);
v_i_4689_ = v___x_4712_;
v_acc_4690_ = v___x_4713_;
goto _start;
}
else
{
goto v___jp_4694_;
}
}
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = lean_unsigned_to_nat(2u);
v___x_4716_ = lean_nat_add(v_i_4689_, v___x_4715_);
lean_dec(v_i_4689_);
lean_inc(v_stx_4693_);
v___x_4717_ = lean_array_push(v_acc_4690_, v_stx_4693_);
v_i_4689_ = v___x_4716_;
v_acc_4690_ = v___x_4717_;
goto _start;
}
}
v___jp_4694_:
{
lean_object* v___x_4695_; lean_object* v_sepStx_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4695_ = lean_nat_pred(v_i_4689_);
v_sepStx_4696_ = lean_array_fget_borrowed(v_a_4687_, v___x_4695_);
lean_dec(v___x_4695_);
v___x_4697_ = lean_unsigned_to_nat(2u);
v___x_4698_ = lean_nat_add(v_i_4689_, v___x_4697_);
lean_dec(v_i_4689_);
lean_inc(v_sepStx_4696_);
v___x_4699_ = lean_array_push(v_acc_4690_, v_sepStx_4696_);
lean_inc(v_stx_4693_);
v___x_4700_ = lean_array_push(v___x_4699_, v_stx_4693_);
v_i_4689_ = v___x_4698_;
v_acc_4690_ = v___x_4700_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4719_, lean_object* v_p_4720_, lean_object* v_i_4721_, lean_object* v_acc_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4719_, v_p_4720_, v_i_4721_, v_acc_4722_);
lean_dec_ref(v_a_4719_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4724_, lean_object* v_p_4725_){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = lean_unsigned_to_nat(0u);
v___x_4727_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4728_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4724_, v_p_4725_, v___x_4726_, v___x_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4729_, lean_object* v_p_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4729_, v_p_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4732_, lean_object* v_p_4733_){
_start:
{
lean_object* v___f_4734_; lean_object* v___x_4735_; 
v___f_4734_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4734_, 0, v_p_4733_);
v___x_4735_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4732_, v___f_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4736_, lean_object* v_p_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Array_filterSepElems(v_a_4736_, v_p_4737_);
lean_dec_ref(v_a_4736_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4739_, lean_object* v_acc_4740_, lean_object* v_inst_4741_, lean_object* v_a_4742_, lean_object* v_f_4743_, lean_object* v_stx_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4739_, v_acc_4740_, v_inst_4741_, v_a_4742_, v_f_4743_, v_stx_4744_);
lean_dec(v_i_4739_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4746_, lean_object* v_a_4747_, lean_object* v_f_4748_, lean_object* v_i_4749_, lean_object* v_acc_4750_){
_start:
{
lean_object* v_toApplicative_4751_; lean_object* v_toBind_4752_; lean_object* v_toPure_4753_; lean_object* v___x_4754_; uint8_t v___x_4755_; 
v_toApplicative_4751_ = lean_ctor_get(v_inst_4746_, 0);
v_toBind_4752_ = lean_ctor_get(v_inst_4746_, 1);
v_toPure_4753_ = lean_ctor_get(v_toApplicative_4751_, 1);
v___x_4754_ = lean_array_get_size(v_a_4747_);
v___x_4755_ = lean_nat_dec_lt(v_i_4749_, v___x_4754_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; 
lean_inc(v_toPure_4753_);
lean_dec(v_i_4749_);
lean_dec(v_f_4748_);
lean_dec_ref(v_a_4747_);
lean_dec_ref(v_inst_4746_);
v___x_4756_ = lean_apply_2(v_toPure_4753_, lean_box(0), v_acc_4750_);
return v___x_4756_;
}
else
{
lean_object* v_stx_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v_stx_4757_ = lean_array_fget_borrowed(v_a_4747_, v_i_4749_);
v___x_4758_ = lean_unsigned_to_nat(2u);
v___x_4759_ = lean_nat_mod(v_i_4749_, v___x_4758_);
v___x_4760_ = lean_unsigned_to_nat(0u);
v___x_4761_ = lean_nat_dec_eq(v___x_4759_, v___x_4760_);
lean_dec(v___x_4759_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4762_ = lean_unsigned_to_nat(1u);
v___x_4763_ = lean_nat_add(v_i_4749_, v___x_4762_);
lean_dec(v_i_4749_);
lean_inc(v_stx_4757_);
v___x_4764_ = lean_array_push(v_acc_4750_, v_stx_4757_);
v_i_4749_ = v___x_4763_;
v_acc_4750_ = v___x_4764_;
goto _start;
}
else
{
lean_object* v___f_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
lean_inc(v_stx_4757_);
lean_inc(v_toBind_4752_);
lean_inc(v_f_4748_);
v___f_4766_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4766_, 0, v_i_4749_);
lean_closure_set(v___f_4766_, 1, v_acc_4750_);
lean_closure_set(v___f_4766_, 2, v_inst_4746_);
lean_closure_set(v___f_4766_, 3, v_a_4747_);
lean_closure_set(v___f_4766_, 4, v_f_4748_);
v___x_4767_ = lean_apply_1(v_f_4748_, v_stx_4757_);
v___x_4768_ = lean_apply_4(v_toBind_4752_, lean_box(0), lean_box(0), v___x_4767_, v___f_4766_);
return v___x_4768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4769_, lean_object* v_acc_4770_, lean_object* v_inst_4771_, lean_object* v_a_4772_, lean_object* v_f_4773_, lean_object* v_stx_4774_){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4775_ = lean_unsigned_to_nat(1u);
v___x_4776_ = lean_nat_add(v_i_4769_, v___x_4775_);
v___x_4777_ = lean_array_push(v_acc_4770_, v_stx_4774_);
v___x_4778_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4771_, v_a_4772_, v_f_4773_, v___x_4776_, v___x_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4779_, lean_object* v_inst_4780_, lean_object* v_a_4781_, lean_object* v_f_4782_, lean_object* v_i_4783_, lean_object* v_acc_4784_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4780_, v_a_4781_, v_f_4782_, v_i_4783_, v_acc_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4786_, lean_object* v_a_4787_, lean_object* v_f_4788_){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = lean_unsigned_to_nat(0u);
v___x_4790_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4791_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4786_, v_a_4787_, v_f_4788_, v___x_4789_, v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4792_, lean_object* v_inst_4793_, lean_object* v_a_4794_, lean_object* v_f_4795_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Array_mapSepElemsM___redArg(v_inst_4793_, v_a_4794_, v_f_4795_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4797_, lean_object* v_x_4798_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = lean_apply_1(v_f_4797_, v_x_4798_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4800_, lean_object* v_f_4801_, lean_object* v_i_4802_, lean_object* v_acc_4803_){
_start:
{
lean_object* v___x_4804_; uint8_t v___x_4805_; 
v___x_4804_ = lean_array_get_size(v_a_4800_);
v___x_4805_ = lean_nat_dec_lt(v_i_4802_, v___x_4804_);
if (v___x_4805_ == 0)
{
lean_dec(v_i_4802_);
lean_dec_ref(v_f_4801_);
return v_acc_4803_;
}
else
{
lean_object* v_stx_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_stx_4806_ = lean_array_fget_borrowed(v_a_4800_, v_i_4802_);
v___x_4807_ = lean_unsigned_to_nat(2u);
v___x_4808_ = lean_nat_mod(v_i_4802_, v___x_4807_);
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = lean_nat_dec_eq(v___x_4808_, v___x_4809_);
lean_dec(v___x_4808_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4811_ = lean_unsigned_to_nat(1u);
v___x_4812_ = lean_nat_add(v_i_4802_, v___x_4811_);
lean_dec(v_i_4802_);
lean_inc(v_stx_4806_);
v___x_4813_ = lean_array_push(v_acc_4803_, v_stx_4806_);
v_i_4802_ = v___x_4812_;
v_acc_4803_ = v___x_4813_;
goto _start;
}
else
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_inc_ref(v_f_4801_);
lean_inc(v_stx_4806_);
v___x_4815_ = lean_apply_1(v_f_4801_, v_stx_4806_);
v___x_4816_ = lean_unsigned_to_nat(1u);
v___x_4817_ = lean_nat_add(v_i_4802_, v___x_4816_);
lean_dec(v_i_4802_);
v___x_4818_ = lean_array_push(v_acc_4803_, v___x_4815_);
v_i_4802_ = v___x_4817_;
v_acc_4803_ = v___x_4818_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4820_, lean_object* v_f_4821_, lean_object* v_i_4822_, lean_object* v_acc_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4820_, v_f_4821_, v_i_4822_, v_acc_4823_);
lean_dec_ref(v_a_4820_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4825_, lean_object* v_f_4826_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = lean_unsigned_to_nat(0u);
v___x_4828_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4829_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4825_, v_f_4826_, v___x_4827_, v___x_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4830_, lean_object* v_f_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4830_, v_f_4831_);
lean_dec_ref(v_a_4830_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4833_, lean_object* v_f_4834_){
_start:
{
lean_object* v___f_4835_; lean_object* v___x_4836_; 
v___f_4835_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4835_, 0, v_f_4834_);
v___x_4836_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4833_, v___f_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4837_, lean_object* v_f_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Array_mapSepElems(v_a_4837_, v_f_4838_);
lean_dec_ref(v_a_4837_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4840_, size_t v_i_4841_, size_t v_stop_4842_, lean_object* v_b_4843_){
_start:
{
lean_object* v___y_4845_; uint8_t v___x_4849_; 
v___x_4849_ = lean_usize_dec_eq(v_i_4841_, v_stop_4842_);
if (v___x_4849_ == 0)
{
lean_object* v_fst_4850_; uint8_t v___x_4851_; 
v_fst_4850_ = lean_ctor_get(v_b_4843_, 0);
v___x_4851_ = lean_unbox(v_fst_4850_);
if (v___x_4851_ == 0)
{
lean_object* v_snd_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4861_; 
v_snd_4852_ = lean_ctor_get(v_b_4843_, 1);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_b_4843_);
if (v_isSharedCheck_4861_ == 0)
{
lean_object* v_unused_4862_; 
v_unused_4862_ = lean_ctor_get(v_b_4843_, 0);
lean_dec(v_unused_4862_);
v___x_4854_ = v_b_4843_;
v_isShared_4855_ = v_isSharedCheck_4861_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_snd_4852_);
lean_dec(v_b_4843_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4861_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; 
v___x_4856_ = 1;
v___x_4857_ = lean_box(v___x_4856_);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4857_);
v___x_4859_ = v___x_4854_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4857_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_snd_4852_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
v___y_4845_ = v___x_4859_;
goto v___jp_4844_;
}
}
}
else
{
lean_object* v_snd_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4873_; 
v_snd_4863_ = lean_ctor_get(v_b_4843_, 1);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_b_4843_);
if (v_isSharedCheck_4873_ == 0)
{
lean_object* v_unused_4874_; 
v_unused_4874_ = lean_ctor_get(v_b_4843_, 0);
lean_dec(v_unused_4874_);
v___x_4865_ = v_b_4843_;
v_isShared_4866_ = v_isSharedCheck_4873_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_snd_4863_);
lean_dec(v_b_4843_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4873_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4867_ = lean_array_uget_borrowed(v_as_4840_, v_i_4841_);
lean_inc(v___x_4867_);
v___x_4868_ = lean_array_push(v_snd_4863_, v___x_4867_);
v___x_4869_ = lean_box(v___x_4849_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 1, v___x_4868_);
lean_ctor_set(v___x_4865_, 0, v___x_4869_);
v___x_4871_ = v___x_4865_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
lean_ctor_set(v_reuseFailAlloc_4872_, 1, v___x_4868_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
v___y_4845_ = v___x_4871_;
goto v___jp_4844_;
}
}
}
}
else
{
return v_b_4843_;
}
v___jp_4844_:
{
size_t v___x_4846_; size_t v___x_4847_; 
v___x_4846_ = ((size_t)1ULL);
v___x_4847_ = lean_usize_add(v_i_4841_, v___x_4846_);
v_i_4841_ = v___x_4847_;
v_b_4843_ = v___y_4845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4875_, lean_object* v_i_4876_, lean_object* v_stop_4877_, lean_object* v_b_4878_){
_start:
{
size_t v_i_boxed_4879_; size_t v_stop_boxed_4880_; lean_object* v_res_4881_; 
v_i_boxed_4879_ = lean_unbox_usize(v_i_4876_);
lean_dec(v_i_4876_);
v_stop_boxed_4880_ = lean_unbox_usize(v_stop_4877_);
lean_dec(v_stop_4877_);
v_res_4881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4875_, v_i_boxed_4879_, v_stop_boxed_4880_, v_b_4878_);
lean_dec_ref(v_as_4875_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4882_){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; uint8_t v___x_4886_; 
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4885_ = lean_array_get_size(v_sa_4882_);
v___x_4886_ = lean_nat_dec_lt(v___x_4883_, v___x_4885_);
if (v___x_4886_ == 0)
{
return v___x_4884_;
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4888_; size_t v___x_4889_; size_t v___x_4890_; lean_object* v___x_4891_; lean_object* v_snd_4892_; 
v___x_4887_ = lean_box(v___x_4886_);
v___x_4888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
lean_ctor_set(v___x_4888_, 1, v___x_4884_);
v___x_4889_ = ((size_t)0ULL);
v___x_4890_ = lean_usize_of_nat(v___x_4885_);
v___x_4891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4882_, v___x_4889_, v___x_4890_, v___x_4888_);
v_snd_4892_ = lean_ctor_get(v___x_4891_, 1);
lean_inc(v_snd_4892_);
lean_dec_ref(v___x_4891_);
return v_snd_4892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4893_);
lean_dec_ref(v_sa_4893_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4895_, lean_object* v_sa_4896_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4898_, lean_object* v_sa_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_Syntax_SepArray_getElems(v_sep_4898_, v_sa_4899_);
lean_dec_ref(v_sa_4899_);
lean_dec_ref(v_sep_4898_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4901_){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; uint8_t v___x_4905_; 
v___x_4902_ = lean_unsigned_to_nat(0u);
v___x_4903_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4904_ = lean_array_get_size(v_sa_4901_);
v___x_4905_ = lean_nat_dec_lt(v___x_4902_, v___x_4904_);
if (v___x_4905_ == 0)
{
return v___x_4903_;
}
else
{
lean_object* v___x_4906_; lean_object* v___x_4907_; size_t v___x_4908_; size_t v___x_4909_; lean_object* v___x_4910_; lean_object* v_snd_4911_; 
v___x_4906_ = lean_box(v___x_4905_);
v___x_4907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
lean_ctor_set(v___x_4907_, 1, v___x_4903_);
v___x_4908_ = ((size_t)0ULL);
v___x_4909_ = lean_usize_of_nat(v___x_4904_);
v___x_4910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4901_, v___x_4908_, v___x_4909_, v___x_4907_);
v_snd_4911_ = lean_ctor_get(v___x_4910_, 1);
lean_inc(v_snd_4911_);
lean_dec_ref(v___x_4910_);
return v_snd_4911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4912_);
lean_dec_ref(v_sa_4912_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4914_, lean_object* v_sep_4915_, lean_object* v_sa_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4918_, lean_object* v_sep_4919_, lean_object* v_sa_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l_Lean_Syntax_TSepArray_getElems(v_k_4918_, v_sep_4919_, v_sa_4920_);
lean_dec_ref(v_sa_4920_);
lean_dec_ref(v_sep_4919_);
lean_dec(v_k_4918_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4922_, lean_object* v_sa_4923_, lean_object* v_e_4924_){
_start:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
v___x_4925_ = lean_array_get_size(v_sa_4923_);
v___x_4926_ = lean_unsigned_to_nat(0u);
v___x_4927_ = lean_nat_dec_eq(v___x_4925_, v___x_4926_);
if (v___x_4927_ == 0)
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4928_ = l_Lean_mkAtom(v_sep_4922_);
v___x_4929_ = lean_array_push(v_sa_4923_, v___x_4928_);
v___x_4930_ = lean_array_push(v___x_4929_, v_e_4924_);
return v___x_4930_;
}
else
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec_ref(v_sa_4923_);
lean_dec_ref(v_sep_4922_);
v___x_4931_ = lean_unsigned_to_nat(1u);
v___x_4932_ = lean_mk_empty_array_with_capacity(v___x_4931_);
v___x_4933_ = lean_array_push(v___x_4932_, v_e_4924_);
return v___x_4933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4934_, lean_object* v_sep_4935_, lean_object* v_sa_4936_, lean_object* v_e_4937_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4935_, v_sa_4936_, v_e_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4939_, lean_object* v_sep_4940_, lean_object* v_sa_4941_, lean_object* v_e_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_Syntax_TSepArray_push(v_k_4939_, v_sep_4940_, v_sa_4941_, v_e_4942_);
lean_dec(v_k_4939_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4945_; 
v___x_4945_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4947_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4948_; 
v___x_4948_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4949_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4951_);
lean_dec_ref(v_sep_4951_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4956_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4958_, lean_object* v_k_4959_){
_start:
{
lean_object* v___x_4960_; 
v___x_4960_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4961_, lean_object* v_k_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4961_, v_k_4962_);
lean_dec_ref(v_k_4962_);
lean_dec(v_sep_4961_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4964_){
_start:
{
lean_inc_ref(v_v_4964_);
return v_v_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4965_);
lean_dec_ref(v_v_4965_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4969_; 
v___f_4969_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4972_, lean_object* v_sep_4973_){
_start:
{
lean_object* v___f_4974_; 
v___f_4974_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4975_, lean_object* v_sep_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4975_, v_sep_4976_);
lean_dec_ref(v_sep_4976_);
lean_dec(v_k_4975_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4978_, lean_object* v_sep_4979_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4980_, 0, v_k_4978_);
lean_closure_set(v___x_4980_, 1, v_sep_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4981_, lean_object* v_x_4982_){
_start:
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_apply_1(v_inst_4981_, v_x_4982_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v___x_4986_; size_t v_sz_4987_; size_t v___x_4988_; lean_object* v___x_4989_; 
v___x_4986_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4987_ = lean_array_size(v_a_4985_);
v___x_4988_ = ((size_t)0ULL);
v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4986_, v___f_4984_, v_sz_4987_, v___x_4988_, v_a_4985_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_4990_){
_start:
{
lean_object* v___f_4991_; lean_object* v___f_4992_; 
v___f_4991_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4991_, 0, v_inst_4990_);
v___f_4992_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4992_, 0, v___f_4991_);
return v___f_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_4993_, lean_object* v_k_x27_4994_, lean_object* v_inst_4995_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_4997_, lean_object* v_k_x27_4998_, lean_object* v_inst_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_4997_, v_k_x27_4998_, v_inst_4999_);
lean_dec(v_k_x27_4998_);
lean_dec(v_k_4997_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_5001_){
_start:
{
lean_inc_ref(v_a_5001_);
return v_a_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_5002_);
lean_dec_ref(v_a_5002_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_5006_; 
v___f_5006_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5009_){
_start:
{
lean_object* v___f_5010_; 
v___f_5010_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5011_);
lean_dec(v_k_5011_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5019_){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5020_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5021_ = lean_box(2);
v___x_5022_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5023_ = lean_unsigned_to_nat(2u);
v___x_5024_ = lean_mk_empty_array_with_capacity(v___x_5023_);
v___x_5025_ = lean_array_push(v___x_5024_, v_id_5019_);
v___x_5026_ = lean_array_push(v___x_5025_, v___x_5022_);
v___x_5027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5021_);
lean_ctor_set(v___x_5027_, 1, v___x_5020_);
lean_ctor_set(v___x_5027_, 2, v___x_5026_);
return v___x_5027_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = 123;
v___x_5032_ = lean_box_uint32(v___x_5031_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5033_, lean_object* v_i_5034_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Lean_Syntax_decodeQuotedChar(v_s_5033_, v_i_5034_);
if (lean_obj_tag(v___x_5035_) == 0)
{
uint32_t v_c_5036_; uint32_t v___x_5037_; uint8_t v___x_5038_; 
v_c_5036_ = lean_string_utf8_get(v_s_5033_, v_i_5034_);
v___x_5037_ = 123;
v___x_5038_ = lean_uint32_dec_eq(v_c_5036_, v___x_5037_);
if (v___x_5038_ == 0)
{
return v___x_5035_;
}
else
{
lean_object* v_i_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v_i_5039_ = lean_string_utf8_next(v_s_5033_, v_i_5034_);
v___x_5040_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5040_);
lean_ctor_set(v___x_5041_, 1, v_i_5039_);
v___x_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5041_);
return v___x_5042_;
}
}
else
{
return v___x_5035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5043_, lean_object* v_i_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5043_, v_i_5044_);
lean_dec(v_i_5044_);
lean_dec_ref(v_s_5043_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5046_, lean_object* v_i_5047_, lean_object* v_acc_5048_){
_start:
{
uint32_t v_c_5049_; uint32_t v___x_5050_; uint8_t v___x_5051_; 
v_c_5049_ = lean_string_utf8_get(v_s_5046_, v_i_5047_);
v___x_5050_ = 34;
v___x_5051_ = lean_uint32_dec_eq(v_c_5049_, v___x_5050_);
if (v___x_5051_ == 0)
{
uint32_t v___x_5052_; uint8_t v___x_5053_; 
v___x_5052_ = 123;
v___x_5053_ = lean_uint32_dec_eq(v_c_5049_, v___x_5052_);
if (v___x_5053_ == 0)
{
lean_object* v_i_5054_; uint8_t v___x_5055_; 
v_i_5054_ = lean_string_utf8_next(v_s_5046_, v_i_5047_);
lean_dec(v_i_5047_);
v___x_5055_ = lean_string_utf8_at_end(v_s_5046_, v_i_5054_);
if (v___x_5055_ == 0)
{
uint32_t v___x_5056_; uint8_t v___x_5057_; 
v___x_5056_ = 92;
v___x_5057_ = lean_uint32_dec_eq(v_c_5049_, v___x_5056_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; 
v___x_5058_ = lean_string_push(v_acc_5048_, v_c_5049_);
v_i_5047_ = v_i_5054_;
v_acc_5048_ = v___x_5058_;
goto _start;
}
else
{
lean_object* v___x_5060_; 
v___x_5060_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5046_, v_i_5054_);
if (lean_obj_tag(v___x_5060_) == 1)
{
lean_object* v_val_5061_; lean_object* v_fst_5062_; lean_object* v_snd_5063_; uint32_t v___x_5064_; lean_object* v___x_5065_; 
lean_dec(v_i_5054_);
v_val_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_val_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v_fst_5062_ = lean_ctor_get(v_val_5061_, 0);
lean_inc(v_fst_5062_);
v_snd_5063_ = lean_ctor_get(v_val_5061_, 1);
lean_inc(v_snd_5063_);
lean_dec(v_val_5061_);
v___x_5064_ = lean_unbox_uint32(v_fst_5062_);
lean_dec(v_fst_5062_);
v___x_5065_ = lean_string_push(v_acc_5048_, v___x_5064_);
v_i_5047_ = v_snd_5063_;
v_acc_5048_ = v___x_5065_;
goto _start;
}
else
{
lean_object* v___x_5067_; 
lean_dec(v___x_5060_);
lean_inc_ref(v_s_5046_);
v___x_5067_ = l_Lean_Syntax_decodeStringGap(v_s_5046_, v_i_5054_);
lean_dec(v_i_5054_);
if (lean_obj_tag(v___x_5067_) == 1)
{
lean_object* v_val_5068_; 
v_val_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_val_5068_);
lean_dec_ref_known(v___x_5067_, 1);
v_i_5047_ = v_val_5068_;
goto _start;
}
else
{
lean_object* v___x_5070_; 
lean_dec(v___x_5067_);
lean_dec_ref(v_acc_5048_);
lean_dec_ref(v_s_5046_);
v___x_5070_ = lean_box(0);
return v___x_5070_;
}
}
}
}
else
{
lean_object* v___x_5071_; 
lean_dec(v_i_5054_);
lean_dec_ref(v_acc_5048_);
lean_dec_ref(v_s_5046_);
v___x_5071_ = lean_box(0);
return v___x_5071_;
}
}
else
{
lean_object* v___x_5072_; 
lean_dec(v_i_5047_);
lean_dec_ref(v_s_5046_);
v___x_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5072_, 0, v_acc_5048_);
return v___x_5072_;
}
}
else
{
lean_object* v___x_5073_; 
lean_dec(v_i_5047_);
lean_dec_ref(v_s_5046_);
v___x_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5073_, 0, v_acc_5048_);
return v___x_5073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5074_){
_start:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5075_ = lean_unsigned_to_nat(1u);
v___x_5076_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5077_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5074_, v___x_5075_, v___x_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5081_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5083_ = l_Lean_Syntax_isLit_x3f(v___x_5082_, v_stx_5081_);
if (lean_obj_tag(v___x_5083_) == 0)
{
return v___x_5083_;
}
else
{
lean_object* v_val_5084_; lean_object* v___x_5085_; 
v_val_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_val_5084_);
lean_dec_ref_known(v___x_5083_, 1);
v___x_5085_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5084_);
return v___x_5085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5086_);
lean_dec(v_stx_5086_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5088_){
_start:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
v___x_5089_ = l_Lean_Syntax_getArgs(v_stx_5088_);
v___x_5090_ = lean_unsigned_to_nat(0u);
v___x_5091_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5092_ = lean_array_get_size(v___x_5089_);
v___x_5093_ = lean_nat_dec_lt(v___x_5090_, v___x_5092_);
if (v___x_5093_ == 0)
{
lean_dec_ref(v___x_5089_);
return v___x_5091_;
}
else
{
lean_object* v___x_5094_; lean_object* v___x_5095_; size_t v___x_5096_; size_t v___x_5097_; lean_object* v___x_5098_; lean_object* v_snd_5099_; 
v___x_5094_ = lean_box(v___x_5093_);
v___x_5095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5094_);
lean_ctor_set(v___x_5095_, 1, v___x_5091_);
v___x_5096_ = ((size_t)0ULL);
v___x_5097_ = lean_usize_of_nat(v___x_5092_);
v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5089_, v___x_5096_, v___x_5097_, v___x_5095_);
lean_dec_ref(v___x_5089_);
v_snd_5099_ = lean_ctor_get(v___x_5098_, 1);
lean_inc(v_snd_5099_);
lean_dec_ref(v___x_5098_);
return v_snd_5099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Syntax_getSepArgs(v_stx_5100_);
lean_dec(v_stx_5100_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5102_, lean_object* v_mkElem_5103_, lean_object* v_mkLit_5104_, lean_object* v_as_5105_, size_t v_sz_5106_, size_t v_i_5107_, lean_object* v_b_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_a_5112_; lean_object* v_a_5113_; lean_object* v_elem_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; uint8_t v___x_5125_; 
v___x_5125_ = lean_usize_dec_lt(v_i_5107_, v_sz_5106_);
if (v___x_5125_ == 0)
{
lean_object* v___x_5126_; 
lean_dec_ref(v_mkLit_5104_);
lean_dec_ref(v_mkElem_5103_);
lean_dec_ref(v_mkAppend_5102_);
v___x_5126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5126_, 0, v_b_5108_);
lean_ctor_set(v___x_5126_, 1, v___y_5110_);
return v___x_5126_;
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5128_; 
v_a_5127_ = lean_array_uget_borrowed(v_as_5105_, v_i_5107_);
v___x_5128_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5127_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v_methods_5129_; lean_object* v_quotContext_5130_; lean_object* v_currMacroScope_5131_; lean_object* v_currRecDepth_5132_; lean_object* v_maxRecDepth_5133_; lean_object* v_ref_5134_; lean_object* v_ref_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v_methods_5129_ = lean_ctor_get(v___y_5109_, 0);
v_quotContext_5130_ = lean_ctor_get(v___y_5109_, 1);
v_currMacroScope_5131_ = lean_ctor_get(v___y_5109_, 2);
v_currRecDepth_5132_ = lean_ctor_get(v___y_5109_, 3);
v_maxRecDepth_5133_ = lean_ctor_get(v___y_5109_, 4);
v_ref_5134_ = lean_ctor_get(v___y_5109_, 5);
v_ref_5135_ = l_Lean_replaceRef(v_a_5127_, v_ref_5134_);
lean_inc(v_maxRecDepth_5133_);
lean_inc(v_currRecDepth_5132_);
lean_inc(v_currMacroScope_5131_);
lean_inc(v_quotContext_5130_);
lean_inc(v_methods_5129_);
v___x_5136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5136_, 0, v_methods_5129_);
lean_ctor_set(v___x_5136_, 1, v_quotContext_5130_);
lean_ctor_set(v___x_5136_, 2, v_currMacroScope_5131_);
lean_ctor_set(v___x_5136_, 3, v_currRecDepth_5132_);
lean_ctor_set(v___x_5136_, 4, v_maxRecDepth_5133_);
lean_ctor_set(v___x_5136_, 5, v_ref_5135_);
lean_inc_ref(v_mkElem_5103_);
lean_inc(v_a_5127_);
v___x_5137_ = lean_apply_3(v_mkElem_5103_, v_a_5127_, v___x_5136_, v___y_5110_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; lean_object* v_a_5139_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_a_5138_);
v_a_5139_ = lean_ctor_get(v___x_5137_, 1);
lean_inc(v_a_5139_);
lean_dec_ref_known(v___x_5137_, 2);
v_elem_5118_ = v_a_5138_;
v___y_5119_ = v___y_5109_;
v___y_5120_ = v_a_5139_;
goto v___jp_5117_;
}
else
{
lean_dec(v_b_5108_);
lean_dec_ref(v_mkLit_5104_);
lean_dec_ref(v_mkElem_5103_);
lean_dec_ref(v_mkAppend_5102_);
return v___x_5137_;
}
}
else
{
lean_object* v_val_5140_; uint8_t v___x_5141_; 
v_val_5140_ = lean_ctor_get(v___x_5128_, 0);
lean_inc_n(v_val_5140_, 2);
lean_dec_ref_known(v___x_5128_, 1);
v___x_5141_ = lean_string_isempty(v_val_5140_);
if (v___x_5141_ == 0)
{
lean_object* v_methods_5142_; lean_object* v_quotContext_5143_; lean_object* v_currMacroScope_5144_; lean_object* v_currRecDepth_5145_; lean_object* v_maxRecDepth_5146_; lean_object* v_ref_5147_; lean_object* v_ref_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; 
v_methods_5142_ = lean_ctor_get(v___y_5109_, 0);
v_quotContext_5143_ = lean_ctor_get(v___y_5109_, 1);
v_currMacroScope_5144_ = lean_ctor_get(v___y_5109_, 2);
v_currRecDepth_5145_ = lean_ctor_get(v___y_5109_, 3);
v_maxRecDepth_5146_ = lean_ctor_get(v___y_5109_, 4);
v_ref_5147_ = lean_ctor_get(v___y_5109_, 5);
v_ref_5148_ = l_Lean_replaceRef(v_a_5127_, v_ref_5147_);
lean_inc(v_maxRecDepth_5146_);
lean_inc(v_currRecDepth_5145_);
lean_inc(v_currMacroScope_5144_);
lean_inc(v_quotContext_5143_);
lean_inc(v_methods_5142_);
v___x_5149_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5149_, 0, v_methods_5142_);
lean_ctor_set(v___x_5149_, 1, v_quotContext_5143_);
lean_ctor_set(v___x_5149_, 2, v_currMacroScope_5144_);
lean_ctor_set(v___x_5149_, 3, v_currRecDepth_5145_);
lean_ctor_set(v___x_5149_, 4, v_maxRecDepth_5146_);
lean_ctor_set(v___x_5149_, 5, v_ref_5148_);
lean_inc_ref(v_mkLit_5104_);
v___x_5150_ = lean_apply_3(v_mkLit_5104_, v_val_5140_, v___x_5149_, v___y_5110_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; lean_object* v_a_5152_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_a_5151_);
v_a_5152_ = lean_ctor_get(v___x_5150_, 1);
lean_inc(v_a_5152_);
lean_dec_ref_known(v___x_5150_, 2);
v_elem_5118_ = v_a_5151_;
v___y_5119_ = v___y_5109_;
v___y_5120_ = v_a_5152_;
goto v___jp_5117_;
}
else
{
lean_dec(v_b_5108_);
lean_dec_ref(v_mkLit_5104_);
lean_dec_ref(v_mkElem_5103_);
lean_dec_ref(v_mkAppend_5102_);
return v___x_5150_;
}
}
else
{
lean_dec(v_val_5140_);
v_a_5112_ = v_b_5108_;
v_a_5113_ = v___y_5110_;
goto v___jp_5111_;
}
}
}
v___jp_5111_:
{
size_t v___x_5114_; size_t v___x_5115_; 
v___x_5114_ = ((size_t)1ULL);
v___x_5115_ = lean_usize_add(v_i_5107_, v___x_5114_);
v_i_5107_ = v___x_5115_;
v_b_5108_ = v_a_5112_;
v___y_5110_ = v_a_5113_;
goto _start;
}
v___jp_5117_:
{
uint8_t v___x_5121_; 
v___x_5121_ = l_Lean_Syntax_isMissing(v_b_5108_);
if (v___x_5121_ == 0)
{
lean_object* v___x_5122_; 
lean_inc_ref(v_mkAppend_5102_);
lean_inc_ref(v___y_5119_);
v___x_5122_ = lean_apply_4(v_mkAppend_5102_, v_b_5108_, v_elem_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v_a_5124_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
v_a_5124_ = lean_ctor_get(v___x_5122_, 1);
lean_inc(v_a_5124_);
lean_dec_ref_known(v___x_5122_, 2);
v_a_5112_ = v_a_5123_;
v_a_5113_ = v_a_5124_;
goto v___jp_5111_;
}
else
{
lean_dec_ref(v_mkLit_5104_);
lean_dec_ref(v_mkElem_5103_);
lean_dec_ref(v_mkAppend_5102_);
return v___x_5122_;
}
}
else
{
lean_dec(v_b_5108_);
v_a_5112_ = v_elem_5118_;
v_a_5113_ = v___y_5120_;
goto v___jp_5111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5153_, lean_object* v_mkElem_5154_, lean_object* v_mkLit_5155_, lean_object* v_as_5156_, lean_object* v_sz_5157_, lean_object* v_i_5158_, lean_object* v_b_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
size_t v_sz_boxed_5162_; size_t v_i_boxed_5163_; lean_object* v_res_5164_; 
v_sz_boxed_5162_ = lean_unbox_usize(v_sz_5157_);
lean_dec(v_sz_5157_);
v_i_boxed_5163_ = lean_unbox_usize(v_i_5158_);
lean_dec(v_i_5158_);
v_res_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5153_, v_mkElem_5154_, v_mkLit_5155_, v_as_5156_, v_sz_boxed_5162_, v_i_boxed_5163_, v_b_5159_, v___y_5160_, v___y_5161_);
lean_dec_ref(v___y_5160_);
lean_dec_ref(v_as_5156_);
return v_res_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5165_, lean_object* v_mkAppend_5166_, lean_object* v_mkElem_5167_, lean_object* v_mkLit_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_){
_start:
{
lean_object* v_result_5171_; size_t v_sz_5172_; size_t v___x_5173_; lean_object* v___x_5174_; 
v_result_5171_ = lean_box(0);
v_sz_5172_ = lean_array_size(v_chunks_5165_);
v___x_5173_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5168_);
v___x_5174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5166_, v_mkElem_5167_, v_mkLit_5168_, v_chunks_5165_, v_sz_5172_, v___x_5173_, v_result_5171_, v_a_5169_, v_a_5170_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v_a_5176_; uint8_t v___x_5177_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
v_a_5176_ = lean_ctor_get(v___x_5174_, 1);
v___x_5177_ = l_Lean_Syntax_isMissing(v_a_5175_);
if (v___x_5177_ == 0)
{
lean_dec_ref(v_mkLit_5168_);
return v___x_5174_;
}
else
{
lean_object* v___x_5178_; lean_object* v___x_5179_; 
lean_inc(v_a_5176_);
lean_dec_ref_known(v___x_5174_, 2);
v___x_5178_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5169_);
v___x_5179_ = lean_apply_3(v_mkLit_5168_, v___x_5178_, v_a_5169_, v_a_5176_);
return v___x_5179_;
}
}
else
{
lean_dec_ref(v_mkLit_5168_);
return v___x_5174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5180_, lean_object* v_mkAppend_5181_, lean_object* v_mkElem_5182_, lean_object* v_mkLit_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5180_, v_mkAppend_5181_, v_mkElem_5182_, v_mkLit_5183_, v_a_5184_, v_a_5185_);
lean_dec_ref(v_a_5184_);
lean_dec_ref(v_chunks_5180_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5191_, lean_object* v_b_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v_ref_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v_ref_5195_ = lean_ctor_get(v___y_5193_, 5);
v___x_5196_ = 0;
v___x_5197_ = l_Lean_SourceInfo_fromRef(v_ref_5195_, v___x_5196_);
v___x_5198_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5199_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5197_);
v___x_5200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5197_);
lean_ctor_set(v___x_5200_, 1, v___x_5199_);
v___x_5201_ = l_Lean_Syntax_node3(v___x_5197_, v___x_5198_, v_a_5191_, v___x_5200_, v_b_5192_);
v___x_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
lean_ctor_set(v___x_5202_, 1, v___y_5194_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5203_, lean_object* v_b_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5203_, v_b_5204_, v___y_5205_, v___y_5206_);
lean_dec_ref(v___y_5205_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5208_, lean_object* v_a_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v_ref_5212_; uint8_t v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v_ref_5212_ = lean_ctor_get(v___y_5210_, 5);
v___x_5213_ = 0;
v___x_5214_ = l_Lean_SourceInfo_fromRef(v_ref_5212_, v___x_5213_);
v___x_5215_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5216_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5214_);
v___x_5217_ = l_Lean_Syntax_node1(v___x_5214_, v___x_5216_, v_a_5209_);
v___x_5218_ = l_Lean_Syntax_node2(v___x_5214_, v___x_5215_, v_ofInterpFn_5208_, v___x_5217_);
v___x_5219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
lean_ctor_set(v___x_5219_, 1, v___y_5211_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5220_, lean_object* v_a_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5220_, v_a_5221_, v___y_5222_, v___y_5223_);
lean_dec_ref(v___y_5222_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5225_, lean_object* v_s_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_ref_5229_; uint8_t v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v_ref_5229_ = lean_ctor_get(v___y_5227_, 5);
v___x_5230_ = 0;
v___x_5231_ = l_Lean_SourceInfo_fromRef(v_ref_5229_, v___x_5230_);
v___x_5232_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5233_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5234_ = lean_box(2);
v___x_5235_ = l_Lean_Syntax_mkStrLit(v_s_5226_, v___x_5234_);
lean_inc(v___x_5231_);
v___x_5236_ = l_Lean_Syntax_node1(v___x_5231_, v___x_5233_, v___x_5235_);
v___x_5237_ = l_Lean_Syntax_node2(v___x_5231_, v___x_5232_, v_ofLitFn_5225_, v___x_5236_);
v___x_5238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5237_);
lean_ctor_set(v___x_5238_, 1, v___y_5228_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5239_, lean_object* v_s_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5239_, v_s_5240_, v___y_5241_, v___y_5242_);
lean_dec_ref(v___y_5241_);
return v_res_5243_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5261_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5262_ = l_String_toRawSubstring_x27(v___x_5261_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5283_, lean_object* v_type_5284_, lean_object* v_ofInterpFn_5285_, lean_object* v_ofLitFn_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___f_5289_; lean_object* v___f_5290_; lean_object* v___f_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___f_5289_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5290_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5290_, 0, v_ofInterpFn_5285_);
v___f_5291_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5291_, 0, v_ofLitFn_5286_);
v___x_5292_ = l_Lean_Syntax_getArgs(v_interpStr_5283_);
v___x_5293_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5292_, v___f_5289_, v___f_5290_, v___f_5291_, v_a_5287_, v_a_5288_);
lean_dec_ref(v___x_5292_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5326_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
v_a_5295_ = lean_ctor_get(v___x_5293_, 1);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5297_ = v___x_5293_;
v_isShared_5298_ = v_isSharedCheck_5326_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_inc(v_a_5294_);
lean_dec(v___x_5293_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5326_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v_quotContext_5299_; lean_object* v_currMacroScope_5300_; lean_object* v_ref_5301_; uint8_t v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5324_; 
v_quotContext_5299_ = lean_ctor_get(v_a_5287_, 1);
v_currMacroScope_5300_ = lean_ctor_get(v_a_5287_, 2);
v_ref_5301_ = lean_ctor_get(v_a_5287_, 5);
v___x_5302_ = 0;
v___x_5303_ = l_Lean_SourceInfo_fromRef(v_ref_5301_, v___x_5302_);
v___x_5304_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5305_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5306_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5303_, 7);
v___x_5307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5303_);
lean_ctor_set(v___x_5307_, 1, v___x_5306_);
v___x_5308_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5309_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5310_ = lean_box(0);
lean_inc(v_currMacroScope_5300_);
lean_inc(v_quotContext_5299_);
v___x_5311_ = l_Lean_addMacroScope(v_quotContext_5299_, v___x_5310_, v_currMacroScope_5300_);
v___x_5312_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5313_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5303_);
lean_ctor_set(v___x_5313_, 1, v___x_5309_);
lean_ctor_set(v___x_5313_, 2, v___x_5311_);
lean_ctor_set(v___x_5313_, 3, v___x_5312_);
v___x_5314_ = l_Lean_Syntax_node1(v___x_5303_, v___x_5308_, v___x_5313_);
v___x_5315_ = l_Lean_Syntax_node2(v___x_5303_, v___x_5305_, v___x_5307_, v___x_5314_);
v___x_5316_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5303_);
lean_ctor_set(v___x_5317_, 1, v___x_5316_);
v___x_5318_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5319_ = l_Lean_Syntax_node1(v___x_5303_, v___x_5318_, v_type_5284_);
v___x_5320_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5303_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = l_Lean_Syntax_node5(v___x_5303_, v___x_5304_, v___x_5315_, v_a_5294_, v___x_5317_, v___x_5319_, v___x_5321_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5322_);
v___x_5324_ = v___x_5297_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
lean_ctor_set(v_reuseFailAlloc_5325_, 1, v_a_5295_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v_a_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5335_; 
lean_dec(v_type_5284_);
v_a_5327_ = lean_ctor_get(v___x_5293_, 0);
v_a_5328_ = lean_ctor_get(v___x_5293_, 1);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5330_ = v___x_5293_;
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_a_5328_);
lean_inc(v_a_5327_);
lean_dec(v___x_5293_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5333_; 
if (v_isShared_5331_ == 0)
{
v___x_5333_ = v___x_5330_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5327_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v_a_5328_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5336_, lean_object* v_type_5337_, lean_object* v_ofInterpFn_5338_, lean_object* v_ofLitFn_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5336_, v_type_5337_, v_ofInterpFn_5338_, v_ofLitFn_5339_, v_a_5340_, v_a_5341_);
lean_dec_ref(v_a_5340_);
lean_dec(v_interpStr_5336_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5343_){
_start:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5344_ = lean_unsigned_to_nat(1u);
v___x_5345_ = l_Lean_Syntax_getArg(v_stx_5343_, v___x_5344_);
if (lean_obj_tag(v___x_5345_) == 1)
{
lean_object* v_kind_5346_; 
v_kind_5346_ = lean_ctor_get(v___x_5345_, 1);
lean_inc(v_kind_5346_);
if (lean_obj_tag(v_kind_5346_) == 1)
{
lean_object* v_pre_5347_; 
v_pre_5347_ = lean_ctor_get(v_kind_5346_, 0);
lean_inc(v_pre_5347_);
if (lean_obj_tag(v_pre_5347_) == 1)
{
lean_object* v_pre_5348_; 
v_pre_5348_ = lean_ctor_get(v_pre_5347_, 0);
lean_inc(v_pre_5348_);
if (lean_obj_tag(v_pre_5348_) == 1)
{
lean_object* v_pre_5349_; 
v_pre_5349_ = lean_ctor_get(v_pre_5348_, 0);
lean_inc(v_pre_5349_);
if (lean_obj_tag(v_pre_5349_) == 1)
{
lean_object* v_pre_5350_; 
v_pre_5350_ = lean_ctor_get(v_pre_5349_, 0);
if (lean_obj_tag(v_pre_5350_) == 0)
{
lean_object* v_args_5351_; lean_object* v_str_5352_; lean_object* v_str_5353_; lean_object* v_str_5354_; lean_object* v_str_5355_; lean_object* v___x_5356_; uint8_t v___x_5357_; 
v_args_5351_ = lean_ctor_get(v___x_5345_, 2);
lean_inc_ref(v_args_5351_);
lean_dec_ref_known(v___x_5345_, 3);
v_str_5352_ = lean_ctor_get(v_kind_5346_, 1);
lean_inc_ref(v_str_5352_);
lean_dec_ref_known(v_kind_5346_, 2);
v_str_5353_ = lean_ctor_get(v_pre_5347_, 1);
lean_inc_ref(v_str_5353_);
lean_dec_ref_known(v_pre_5347_, 2);
v_str_5354_ = lean_ctor_get(v_pre_5348_, 1);
lean_inc_ref(v_str_5354_);
lean_dec_ref_known(v_pre_5348_, 2);
v_str_5355_ = lean_ctor_get(v_pre_5349_, 1);
lean_inc_ref(v_str_5355_);
lean_dec_ref_known(v_pre_5349_, 2);
v___x_5356_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5357_ = lean_string_dec_eq(v_str_5355_, v___x_5356_);
lean_dec_ref(v_str_5355_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; 
lean_dec_ref(v_str_5354_);
lean_dec_ref(v_str_5353_);
lean_dec_ref(v_str_5352_);
lean_dec_ref(v_args_5351_);
v___x_5358_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5358_;
}
else
{
lean_object* v___x_5359_; uint8_t v___x_5360_; 
v___x_5359_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5360_ = lean_string_dec_eq(v_str_5354_, v___x_5359_);
lean_dec_ref(v_str_5354_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; 
lean_dec_ref(v_str_5353_);
lean_dec_ref(v_str_5352_);
lean_dec_ref(v_args_5351_);
v___x_5361_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5361_;
}
else
{
lean_object* v___x_5362_; uint8_t v___x_5363_; 
v___x_5362_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5363_ = lean_string_dec_eq(v_str_5353_, v___x_5362_);
lean_dec_ref(v_str_5353_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; 
lean_dec_ref(v_str_5352_);
lean_dec_ref(v_args_5351_);
v___x_5364_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5364_;
}
else
{
lean_object* v___x_5365_; uint8_t v___x_5366_; 
v___x_5365_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5366_ = lean_string_dec_eq(v_str_5352_, v___x_5365_);
lean_dec_ref(v_str_5352_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; 
lean_dec_ref(v_args_5351_);
v___x_5367_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5367_;
}
else
{
lean_object* v___x_5368_; lean_object* v___x_5369_; uint8_t v___x_5370_; 
v___x_5368_ = lean_array_get_size(v_args_5351_);
v___x_5369_ = lean_unsigned_to_nat(2u);
v___x_5370_ = lean_nat_dec_eq(v___x_5368_, v___x_5369_);
if (v___x_5370_ == 0)
{
lean_object* v___x_5371_; 
lean_dec_ref(v_args_5351_);
v___x_5371_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5371_;
}
else
{
lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5372_ = lean_unsigned_to_nat(0u);
v___x_5373_ = lean_array_fget(v_args_5351_, v___x_5372_);
lean_dec_ref(v_args_5351_);
if (lean_obj_tag(v___x_5373_) == 2)
{
lean_object* v_val_5374_; 
v_val_5374_ = lean_ctor_get(v___x_5373_, 1);
lean_inc_ref(v_val_5374_);
lean_dec_ref_known(v___x_5373_, 2);
return v_val_5374_;
}
else
{
lean_object* v___x_5375_; 
lean_dec(v___x_5373_);
v___x_5375_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5375_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5376_; 
lean_dec_ref_known(v_pre_5349_, 2);
lean_dec_ref_known(v_pre_5348_, 2);
lean_dec_ref_known(v_pre_5347_, 2);
lean_dec_ref_known(v_kind_5346_, 2);
lean_dec_ref_known(v___x_5345_, 3);
v___x_5376_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5376_;
}
}
else
{
lean_object* v___x_5377_; 
lean_dec_ref_known(v_pre_5348_, 2);
lean_dec(v_pre_5349_);
lean_dec_ref_known(v_pre_5347_, 2);
lean_dec_ref_known(v_kind_5346_, 2);
lean_dec_ref_known(v___x_5345_, 3);
v___x_5377_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5377_;
}
}
else
{
lean_object* v___x_5378_; 
lean_dec(v_pre_5348_);
lean_dec_ref_known(v_pre_5347_, 2);
lean_dec_ref_known(v_kind_5346_, 2);
lean_dec_ref_known(v___x_5345_, 3);
v___x_5378_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5378_;
}
}
else
{
lean_object* v___x_5379_; 
lean_dec_ref_known(v_kind_5346_, 2);
lean_dec(v_pre_5347_);
lean_dec_ref_known(v___x_5345_, 3);
v___x_5379_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5379_;
}
}
else
{
lean_object* v___x_5380_; 
lean_dec(v_kind_5346_);
lean_dec_ref_known(v___x_5345_, 3);
v___x_5380_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5380_;
}
}
else
{
lean_object* v___x_5381_; 
lean_dec(v___x_5345_);
v___x_5381_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Lean_TSyntax_getDocString(v_stx_5382_);
lean_dec(v_stx_5382_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5402_, lean_object* v_prec_5403_){
_start:
{
lean_object* v___y_5405_; lean_object* v___y_5412_; lean_object* v___y_5419_; lean_object* v___y_5426_; lean_object* v___y_5433_; lean_object* v___y_5440_; 
switch(v_x_5402_)
{
case 0:
{
lean_object* v___x_5446_; uint8_t v___x_5447_; 
v___x_5446_ = lean_unsigned_to_nat(1024u);
v___x_5447_ = lean_nat_dec_le(v___x_5446_, v_prec_5403_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; 
v___x_5448_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5405_ = v___x_5448_;
goto v___jp_5404_;
}
else
{
lean_object* v___x_5449_; 
v___x_5449_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5405_ = v___x_5449_;
goto v___jp_5404_;
}
}
case 1:
{
lean_object* v___x_5450_; uint8_t v___x_5451_; 
v___x_5450_ = lean_unsigned_to_nat(1024u);
v___x_5451_ = lean_nat_dec_le(v___x_5450_, v_prec_5403_);
if (v___x_5451_ == 0)
{
lean_object* v___x_5452_; 
v___x_5452_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5412_ = v___x_5452_;
goto v___jp_5411_;
}
else
{
lean_object* v___x_5453_; 
v___x_5453_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5412_ = v___x_5453_;
goto v___jp_5411_;
}
}
case 2:
{
lean_object* v___x_5454_; uint8_t v___x_5455_; 
v___x_5454_ = lean_unsigned_to_nat(1024u);
v___x_5455_ = lean_nat_dec_le(v___x_5454_, v_prec_5403_);
if (v___x_5455_ == 0)
{
lean_object* v___x_5456_; 
v___x_5456_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5419_ = v___x_5456_;
goto v___jp_5418_;
}
else
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5419_ = v___x_5457_;
goto v___jp_5418_;
}
}
case 3:
{
lean_object* v___x_5458_; uint8_t v___x_5459_; 
v___x_5458_ = lean_unsigned_to_nat(1024u);
v___x_5459_ = lean_nat_dec_le(v___x_5458_, v_prec_5403_);
if (v___x_5459_ == 0)
{
lean_object* v___x_5460_; 
v___x_5460_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5426_ = v___x_5460_;
goto v___jp_5425_;
}
else
{
lean_object* v___x_5461_; 
v___x_5461_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5426_ = v___x_5461_;
goto v___jp_5425_;
}
}
case 4:
{
lean_object* v___x_5462_; uint8_t v___x_5463_; 
v___x_5462_ = lean_unsigned_to_nat(1024u);
v___x_5463_ = lean_nat_dec_le(v___x_5462_, v_prec_5403_);
if (v___x_5463_ == 0)
{
lean_object* v___x_5464_; 
v___x_5464_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5433_ = v___x_5464_;
goto v___jp_5432_;
}
else
{
lean_object* v___x_5465_; 
v___x_5465_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5433_ = v___x_5465_;
goto v___jp_5432_;
}
}
default: 
{
lean_object* v___x_5466_; uint8_t v___x_5467_; 
v___x_5466_ = lean_unsigned_to_nat(1024u);
v___x_5467_ = lean_nat_dec_le(v___x_5466_, v_prec_5403_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; 
v___x_5468_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5440_ = v___x_5468_;
goto v___jp_5439_;
}
else
{
lean_object* v___x_5469_; 
v___x_5469_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5440_ = v___x_5469_;
goto v___jp_5439_;
}
}
}
v___jp_5404_:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5406_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5405_);
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
lean_inc(v___y_5412_);
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
lean_inc(v___y_5419_);
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
lean_inc(v___y_5426_);
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
lean_inc(v___y_5433_);
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
v___jp_5439_:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; uint8_t v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v___x_5441_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5440_);
v___x_5442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5442_, 0, v___y_5440_);
lean_ctor_set(v___x_5442_, 1, v___x_5441_);
v___x_5443_ = 0;
v___x_5444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5444_, 0, v___x_5442_);
lean_ctor_set_uint8(v___x_5444_, sizeof(void*)*1, v___x_5443_);
v___x_5445_ = l_Repr_addAppParen(v___x_5444_, v_prec_5403_);
return v___x_5445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5470_, lean_object* v_prec_5471_){
_start:
{
uint8_t v_x_329__boxed_5472_; lean_object* v_res_5473_; 
v_x_329__boxed_5472_ = lean_unbox(v_x_5470_);
v_res_5473_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5472_, v_prec_5471_);
lean_dec(v_prec_5471_);
return v_res_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5485_, lean_object* v_prec_5486_){
_start:
{
lean_object* v___y_5488_; lean_object* v___y_5495_; lean_object* v___y_5502_; 
switch(v_x_5485_)
{
case 0:
{
lean_object* v___x_5508_; uint8_t v___x_5509_; 
v___x_5508_ = lean_unsigned_to_nat(1024u);
v___x_5509_ = lean_nat_dec_le(v___x_5508_, v_prec_5486_);
if (v___x_5509_ == 0)
{
lean_object* v___x_5510_; 
v___x_5510_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5488_ = v___x_5510_;
goto v___jp_5487_;
}
else
{
lean_object* v___x_5511_; 
v___x_5511_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5488_ = v___x_5511_;
goto v___jp_5487_;
}
}
case 1:
{
lean_object* v___x_5512_; uint8_t v___x_5513_; 
v___x_5512_ = lean_unsigned_to_nat(1024u);
v___x_5513_ = lean_nat_dec_le(v___x_5512_, v_prec_5486_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5514_; 
v___x_5514_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5495_ = v___x_5514_;
goto v___jp_5494_;
}
else
{
lean_object* v___x_5515_; 
v___x_5515_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5495_ = v___x_5515_;
goto v___jp_5494_;
}
}
default: 
{
lean_object* v___x_5516_; uint8_t v___x_5517_; 
v___x_5516_ = lean_unsigned_to_nat(1024u);
v___x_5517_ = lean_nat_dec_le(v___x_5516_, v_prec_5486_);
if (v___x_5517_ == 0)
{
lean_object* v___x_5518_; 
v___x_5518_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5502_ = v___x_5518_;
goto v___jp_5501_;
}
else
{
lean_object* v___x_5519_; 
v___x_5519_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5502_ = v___x_5519_;
goto v___jp_5501_;
}
}
}
v___jp_5487_:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; uint8_t v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5489_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5488_);
v___x_5490_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5490_, 0, v___y_5488_);
lean_ctor_set(v___x_5490_, 1, v___x_5489_);
v___x_5491_ = 0;
v___x_5492_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5492_, 0, v___x_5490_);
lean_ctor_set_uint8(v___x_5492_, sizeof(void*)*1, v___x_5491_);
v___x_5493_ = l_Repr_addAppParen(v___x_5492_, v_prec_5486_);
return v___x_5493_;
}
v___jp_5494_:
{
lean_object* v___x_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
v___x_5496_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5495_);
v___x_5497_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5497_, 0, v___y_5495_);
lean_ctor_set(v___x_5497_, 1, v___x_5496_);
v___x_5498_ = 0;
v___x_5499_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5499_, 0, v___x_5497_);
lean_ctor_set_uint8(v___x_5499_, sizeof(void*)*1, v___x_5498_);
v___x_5500_ = l_Repr_addAppParen(v___x_5499_, v_prec_5486_);
return v___x_5500_;
}
v___jp_5501_:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; uint8_t v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___x_5503_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5502_);
v___x_5504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5504_, 0, v___y_5502_);
lean_ctor_set(v___x_5504_, 1, v___x_5503_);
v___x_5505_ = 0;
v___x_5506_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5506_, 0, v___x_5504_);
lean_ctor_set_uint8(v___x_5506_, sizeof(void*)*1, v___x_5505_);
v___x_5507_ = l_Repr_addAppParen(v___x_5506_, v_prec_5486_);
return v___x_5507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5520_, lean_object* v_prec_5521_){
_start:
{
uint8_t v_x_167__boxed_5522_; lean_object* v_res_5523_; 
v_x_167__boxed_5522_ = lean_unbox(v_x_5520_);
v_res_5523_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5522_, v_prec_5521_);
lean_dec(v_prec_5521_);
return v_res_5523_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; 
v___x_5535_ = lean_unsigned_to_nat(8u);
v___x_5536_ = lean_nat_to_int(v___x_5535_);
return v___x_5536_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5546_ = lean_unsigned_to_nat(13u);
v___x_5547_ = lean_nat_to_int(v___x_5546_);
return v___x_5547_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5557_ = lean_unsigned_to_nat(10u);
v___x_5558_ = lean_nat_to_int(v___x_5557_);
return v___x_5558_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5562_ = lean_unsigned_to_nat(14u);
v___x_5563_ = lean_nat_to_int(v___x_5562_);
return v___x_5563_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; 
v___x_5567_ = lean_unsigned_to_nat(19u);
v___x_5568_ = lean_nat_to_int(v___x_5567_);
return v___x_5568_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5572_ = lean_unsigned_to_nat(20u);
v___x_5573_ = lean_nat_to_int(v___x_5572_);
return v___x_5573_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5580_ = lean_unsigned_to_nat(9u);
v___x_5581_ = lean_nat_to_int(v___x_5580_);
return v___x_5581_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_unsigned_to_nat(12u);
v___x_5589_ = lean_nat_to_int(v___x_5588_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5596_){
_start:
{
uint8_t v_zeta_5597_; uint8_t v_beta_5598_; uint8_t v_eta_5599_; uint8_t v_etaStruct_5600_; uint8_t v_iota_5601_; uint8_t v_proj_5602_; uint8_t v_decide_5603_; uint8_t v_autoUnfold_5604_; uint8_t v_failIfUnchanged_5605_; uint8_t v_unfoldPartialApp_5606_; uint8_t v_zetaDelta_5607_; uint8_t v_index_5608_; uint8_t v_zetaUnused_5609_; uint8_t v_zetaHave_5610_; uint8_t v_locals_5611_; uint8_t v_instances_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; uint8_t v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; 
v_zeta_5597_ = lean_ctor_get_uint8(v_x_5596_, 0);
v_beta_5598_ = lean_ctor_get_uint8(v_x_5596_, 1);
v_eta_5599_ = lean_ctor_get_uint8(v_x_5596_, 2);
v_etaStruct_5600_ = lean_ctor_get_uint8(v_x_5596_, 3);
v_iota_5601_ = lean_ctor_get_uint8(v_x_5596_, 4);
v_proj_5602_ = lean_ctor_get_uint8(v_x_5596_, 5);
v_decide_5603_ = lean_ctor_get_uint8(v_x_5596_, 6);
v_autoUnfold_5604_ = lean_ctor_get_uint8(v_x_5596_, 7);
v_failIfUnchanged_5605_ = lean_ctor_get_uint8(v_x_5596_, 8);
v_unfoldPartialApp_5606_ = lean_ctor_get_uint8(v_x_5596_, 9);
v_zetaDelta_5607_ = lean_ctor_get_uint8(v_x_5596_, 10);
v_index_5608_ = lean_ctor_get_uint8(v_x_5596_, 11);
v_zetaUnused_5609_ = lean_ctor_get_uint8(v_x_5596_, 12);
v_zetaHave_5610_ = lean_ctor_get_uint8(v_x_5596_, 13);
v_locals_5611_ = lean_ctor_get_uint8(v_x_5596_, 14);
v_instances_5612_ = lean_ctor_get_uint8(v_x_5596_, 15);
v___x_5613_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5614_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5615_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5616_ = lean_unsigned_to_nat(0u);
v___x_5617_ = l_Bool_repr___redArg(v_zeta_5597_);
v___x_5618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5615_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = 0;
v___x_5620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5620_, 0, v___x_5618_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*1, v___x_5619_);
v___x_5621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5614_);
lean_ctor_set(v___x_5621_, 1, v___x_5620_);
v___x_5622_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5621_);
lean_ctor_set(v___x_5623_, 1, v___x_5622_);
v___x_5624_ = lean_box(1);
v___x_5625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5623_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5625_);
lean_ctor_set(v___x_5627_, 1, v___x_5626_);
v___x_5628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5627_);
lean_ctor_set(v___x_5628_, 1, v___x_5613_);
v___x_5629_ = l_Bool_repr___redArg(v_beta_5598_);
v___x_5630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5615_);
lean_ctor_set(v___x_5630_, 1, v___x_5629_);
v___x_5631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5631_, 0, v___x_5630_);
lean_ctor_set_uint8(v___x_5631_, sizeof(void*)*1, v___x_5619_);
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5628_);
lean_ctor_set(v___x_5632_, 1, v___x_5631_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v___x_5622_);
v___x_5634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5633_);
lean_ctor_set(v___x_5634_, 1, v___x_5624_);
v___x_5635_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set(v___x_5637_, 1, v___x_5613_);
v___x_5638_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5639_ = l_Bool_repr___redArg(v_eta_5599_);
v___x_5640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5638_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
lean_ctor_set_uint8(v___x_5641_, sizeof(void*)*1, v___x_5619_);
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5637_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
lean_ctor_set(v___x_5643_, 1, v___x_5622_);
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5643_);
lean_ctor_set(v___x_5644_, 1, v___x_5624_);
v___x_5645_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5644_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set(v___x_5647_, 1, v___x_5613_);
v___x_5648_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5649_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5600_, v___x_5616_);
v___x_5650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5648_);
lean_ctor_set(v___x_5650_, 1, v___x_5649_);
v___x_5651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set_uint8(v___x_5651_, sizeof(void*)*1, v___x_5619_);
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5647_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5622_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v___x_5624_);
v___x_5655_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set(v___x_5657_, 1, v___x_5613_);
v___x_5658_ = l_Bool_repr___redArg(v_iota_5601_);
v___x_5659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5615_);
lean_ctor_set(v___x_5659_, 1, v___x_5658_);
v___x_5660_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set_uint8(v___x_5660_, sizeof(void*)*1, v___x_5619_);
v___x_5661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5657_);
lean_ctor_set(v___x_5661_, 1, v___x_5660_);
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
lean_ctor_set(v___x_5662_, 1, v___x_5622_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___x_5624_);
v___x_5664_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5663_);
lean_ctor_set(v___x_5665_, 1, v___x_5664_);
v___x_5666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
lean_ctor_set(v___x_5666_, 1, v___x_5613_);
v___x_5667_ = l_Bool_repr___redArg(v_proj_5602_);
v___x_5668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5615_);
lean_ctor_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set_uint8(v___x_5669_, sizeof(void*)*1, v___x_5619_);
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5666_);
lean_ctor_set(v___x_5670_, 1, v___x_5669_);
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set(v___x_5671_, 1, v___x_5622_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
lean_ctor_set(v___x_5672_, 1, v___x_5624_);
v___x_5673_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5672_);
lean_ctor_set(v___x_5674_, 1, v___x_5673_);
v___x_5675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set(v___x_5675_, 1, v___x_5613_);
v___x_5676_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5677_ = l_Bool_repr___redArg(v_decide_5603_);
v___x_5678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5676_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*1, v___x_5619_);
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5675_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5680_);
lean_ctor_set(v___x_5681_, 1, v___x_5622_);
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set(v___x_5682_, 1, v___x_5624_);
v___x_5683_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5682_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set(v___x_5685_, 1, v___x_5613_);
v___x_5686_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5687_ = l_Bool_repr___redArg(v_autoUnfold_5604_);
v___x_5688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5686_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5689_, 0, v___x_5688_);
lean_ctor_set_uint8(v___x_5689_, sizeof(void*)*1, v___x_5619_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5685_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5622_);
v___x_5692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
lean_ctor_set(v___x_5692_, 1, v___x_5624_);
v___x_5693_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5613_);
v___x_5696_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5697_ = l_Bool_repr___redArg(v_failIfUnchanged_5605_);
v___x_5698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set_uint8(v___x_5699_, sizeof(void*)*1, v___x_5619_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5695_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
lean_ctor_set(v___x_5701_, 1, v___x_5622_);
v___x_5702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5701_);
lean_ctor_set(v___x_5702_, 1, v___x_5624_);
v___x_5703_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5702_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v___x_5613_);
v___x_5706_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5707_ = l_Bool_repr___redArg(v_unfoldPartialApp_5606_);
v___x_5708_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5706_);
lean_ctor_set(v___x_5708_, 1, v___x_5707_);
v___x_5709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set_uint8(v___x_5709_, sizeof(void*)*1, v___x_5619_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5705_);
lean_ctor_set(v___x_5710_, 1, v___x_5709_);
v___x_5711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set(v___x_5711_, 1, v___x_5622_);
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
lean_ctor_set(v___x_5712_, 1, v___x_5624_);
v___x_5713_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5712_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set(v___x_5715_, 1, v___x_5613_);
v___x_5716_ = l_Bool_repr___redArg(v_zetaDelta_5607_);
v___x_5717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5648_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set_uint8(v___x_5718_, sizeof(void*)*1, v___x_5619_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5715_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
v___x_5720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5719_);
lean_ctor_set(v___x_5720_, 1, v___x_5622_);
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set(v___x_5721_, 1, v___x_5624_);
v___x_5722_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5721_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5723_);
lean_ctor_set(v___x_5724_, 1, v___x_5613_);
v___x_5725_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5726_ = l_Bool_repr___redArg(v_index_5608_);
v___x_5727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5725_);
lean_ctor_set(v___x_5727_, 1, v___x_5726_);
v___x_5728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
lean_ctor_set_uint8(v___x_5728_, sizeof(void*)*1, v___x_5619_);
v___x_5729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5724_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5729_);
lean_ctor_set(v___x_5730_, 1, v___x_5622_);
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
lean_ctor_set(v___x_5731_, 1, v___x_5624_);
v___x_5732_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5731_);
lean_ctor_set(v___x_5733_, 1, v___x_5732_);
v___x_5734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5733_);
lean_ctor_set(v___x_5734_, 1, v___x_5613_);
v___x_5735_ = l_Bool_repr___redArg(v_zetaUnused_5609_);
v___x_5736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5686_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set_uint8(v___x_5737_, sizeof(void*)*1, v___x_5619_);
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5734_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
lean_ctor_set(v___x_5739_, 1, v___x_5622_);
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5739_);
lean_ctor_set(v___x_5740_, 1, v___x_5624_);
v___x_5741_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5740_);
lean_ctor_set(v___x_5742_, 1, v___x_5741_);
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5742_);
lean_ctor_set(v___x_5743_, 1, v___x_5613_);
v___x_5744_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5745_ = l_Bool_repr___redArg(v_zetaHave_5610_);
v___x_5746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5744_);
lean_ctor_set(v___x_5746_, 1, v___x_5745_);
v___x_5747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5747_, 0, v___x_5746_);
lean_ctor_set_uint8(v___x_5747_, sizeof(void*)*1, v___x_5619_);
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5743_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v___x_5749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5748_);
lean_ctor_set(v___x_5749_, 1, v___x_5622_);
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set(v___x_5750_, 1, v___x_5624_);
v___x_5751_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5750_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___x_5753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
lean_ctor_set(v___x_5753_, 1, v___x_5613_);
v___x_5754_ = l_Bool_repr___redArg(v_locals_5611_);
v___x_5755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5676_);
lean_ctor_set(v___x_5755_, 1, v___x_5754_);
v___x_5756_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
lean_ctor_set_uint8(v___x_5756_, sizeof(void*)*1, v___x_5619_);
v___x_5757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5753_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
lean_ctor_set(v___x_5758_, 1, v___x_5622_);
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5758_);
lean_ctor_set(v___x_5759_, 1, v___x_5624_);
v___x_5760_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5759_);
lean_ctor_set(v___x_5761_, 1, v___x_5760_);
v___x_5762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5761_);
lean_ctor_set(v___x_5762_, 1, v___x_5613_);
v___x_5763_ = l_Bool_repr___redArg(v_instances_5612_);
v___x_5764_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5648_);
lean_ctor_set(v___x_5764_, 1, v___x_5763_);
v___x_5765_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5765_, 0, v___x_5764_);
lean_ctor_set_uint8(v___x_5765_, sizeof(void*)*1, v___x_5619_);
v___x_5766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5762_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5768_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5769_, 0, v___x_5768_);
lean_ctor_set(v___x_5769_, 1, v___x_5766_);
v___x_5770_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5771_, 0, v___x_5769_);
lean_ctor_set(v___x_5771_, 1, v___x_5770_);
v___x_5772_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5767_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5773_, 0, v___x_5772_);
lean_ctor_set_uint8(v___x_5773_, sizeof(void*)*1, v___x_5619_);
return v___x_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5774_);
lean_dec_ref(v_x_5774_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5776_, lean_object* v_prec_5777_){
_start:
{
lean_object* v___x_5778_; 
v___x_5778_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5776_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5779_, lean_object* v_prec_5780_){
_start:
{
lean_object* v_res_5781_; 
v_res_5781_ = l_Lean_Meta_instReprConfig_repr(v_x_5779_, v_prec_5780_);
lean_dec(v_prec_5780_);
lean_dec_ref(v_x_5779_);
return v_res_5781_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5789_, lean_object* v_x_5790_){
_start:
{
if (lean_obj_tag(v_x_5789_) == 0)
{
lean_object* v___x_5791_; 
v___x_5791_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5791_;
}
else
{
lean_object* v_val_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5803_; 
v_val_5792_ = lean_ctor_get(v_x_5789_, 0);
v_isSharedCheck_5803_ = !lean_is_exclusive(v_x_5789_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5794_ = v_x_5789_;
v_isShared_5795_ = v_isSharedCheck_5803_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_val_5792_);
lean_dec(v_x_5789_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5803_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5799_; 
v___x_5796_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5797_ = l_Nat_reprFast(v_val_5792_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set_tag(v___x_5794_, 3);
lean_ctor_set(v___x_5794_, 0, v___x_5797_);
v___x_5799_ = v___x_5794_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5797_);
v___x_5799_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
lean_object* v___x_5800_; lean_object* v___x_5801_; 
v___x_5800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5796_);
lean_ctor_set(v___x_5800_, 1, v___x_5799_);
v___x_5801_ = l_Repr_addAppParen(v___x_5800_, v_x_5790_);
return v___x_5801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5804_, lean_object* v_x_5805_){
_start:
{
lean_object* v_res_5806_; 
v_res_5806_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5804_, v_x_5805_);
lean_dec(v_x_5805_);
return v_res_5806_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5819_ = lean_unsigned_to_nat(21u);
v___x_5820_ = lean_nat_to_int(v___x_5819_);
return v___x_5820_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5827_ = lean_unsigned_to_nat(11u);
v___x_5828_ = lean_nat_to_int(v___x_5827_);
return v___x_5828_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5844_ = lean_unsigned_to_nat(23u);
v___x_5845_ = lean_nat_to_int(v___x_5844_);
return v___x_5845_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = lean_unsigned_to_nat(16u);
v___x_5850_ = lean_nat_to_int(v___x_5849_);
return v___x_5850_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = lean_unsigned_to_nat(15u);
v___x_5858_ = lean_nat_to_int(v___x_5857_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_unsigned_to_nat(17u);
v___x_5866_ = lean_nat_to_int(v___x_5865_);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5873_ = lean_unsigned_to_nat(18u);
v___x_5874_ = lean_nat_to_int(v___x_5873_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5875_){
_start:
{
lean_object* v_maxSteps_5876_; lean_object* v_maxDischargeDepth_5877_; uint8_t v_contextual_5878_; uint8_t v_memoize_5879_; uint8_t v_singlePass_5880_; uint8_t v_zeta_5881_; uint8_t v_beta_5882_; uint8_t v_eta_5883_; uint8_t v_etaStruct_5884_; uint8_t v_iota_5885_; uint8_t v_proj_5886_; uint8_t v_decide_5887_; uint8_t v_arith_5888_; uint8_t v_autoUnfold_5889_; uint8_t v_dsimp_5890_; uint8_t v_failIfUnchanged_5891_; uint8_t v_ground_5892_; uint8_t v_unfoldPartialApp_5893_; uint8_t v_zetaDelta_5894_; uint8_t v_index_5895_; uint8_t v_implicitDefEqProofs_5896_; uint8_t v_zetaUnused_5897_; uint8_t v_catchRuntime_5898_; uint8_t v_zetaHave_5899_; uint8_t v_letToHave_5900_; uint8_t v_congrConsts_5901_; uint8_t v_bitVecOfNat_5902_; uint8_t v_warnExponents_5903_; uint8_t v_suggestions_5904_; lean_object* v_maxSuggestions_5905_; uint8_t v_locals_5906_; uint8_t v_instances_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; uint8_t v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; 
v_maxSteps_5876_ = lean_ctor_get(v_x_5875_, 0);
lean_inc(v_maxSteps_5876_);
v_maxDischargeDepth_5877_ = lean_ctor_get(v_x_5875_, 1);
lean_inc(v_maxDischargeDepth_5877_);
v_contextual_5878_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3);
v_memoize_5879_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 1);
v_singlePass_5880_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 2);
v_zeta_5881_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 3);
v_beta_5882_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 4);
v_eta_5883_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 5);
v_etaStruct_5884_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 6);
v_iota_5885_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 7);
v_proj_5886_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 8);
v_decide_5887_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 9);
v_arith_5888_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 10);
v_autoUnfold_5889_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 11);
v_dsimp_5890_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5891_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 13);
v_ground_5892_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5893_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 15);
v_zetaDelta_5894_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 16);
v_index_5895_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5896_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 18);
v_zetaUnused_5897_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 19);
v_catchRuntime_5898_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 20);
v_zetaHave_5899_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 21);
v_letToHave_5900_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 22);
v_congrConsts_5901_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5902_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 24);
v_warnExponents_5903_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 25);
v_suggestions_5904_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 26);
v_maxSuggestions_5905_ = lean_ctor_get(v_x_5875_, 2);
lean_inc(v_maxSuggestions_5905_);
v_locals_5906_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 27);
v_instances_5907_ = lean_ctor_get_uint8(v_x_5875_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5875_);
v___x_5908_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5909_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5910_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5911_ = l_Nat_reprFast(v_maxSteps_5876_);
v___x_5912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
v___x_5913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5910_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
v___x_5914_ = 0;
v___x_5915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set_uint8(v___x_5915_, sizeof(void*)*1, v___x_5914_);
v___x_5916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5909_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5916_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
v___x_5919_ = lean_box(1);
v___x_5920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5918_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
v___x_5921_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5920_);
lean_ctor_set(v___x_5922_, 1, v___x_5921_);
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
lean_ctor_set(v___x_5923_, 1, v___x_5908_);
v___x_5924_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5925_ = l_Nat_reprFast(v_maxDischargeDepth_5877_);
v___x_5926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5924_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
v___x_5928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*1, v___x_5914_);
v___x_5929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5923_);
lean_ctor_set(v___x_5929_, 1, v___x_5928_);
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
lean_ctor_set(v___x_5930_, 1, v___x_5917_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5919_);
v___x_5932_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5931_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5908_);
v___x_5935_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5936_ = lean_unsigned_to_nat(0u);
v___x_5937_ = l_Bool_repr___redArg(v_contextual_5878_);
v___x_5938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5935_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5914_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5934_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5917_);
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5941_);
lean_ctor_set(v___x_5942_, 1, v___x_5919_);
v___x_5943_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set(v___x_5945_, 1, v___x_5908_);
v___x_5946_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5947_ = l_Bool_repr___redArg(v_memoize_5879_);
v___x_5948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5946_);
lean_ctor_set(v___x_5948_, 1, v___x_5947_);
v___x_5949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set_uint8(v___x_5949_, sizeof(void*)*1, v___x_5914_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5945_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set(v___x_5951_, 1, v___x_5917_);
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
lean_ctor_set(v___x_5952_, 1, v___x_5919_);
v___x_5953_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5952_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set(v___x_5955_, 1, v___x_5908_);
v___x_5956_ = l_Bool_repr___redArg(v_singlePass_5880_);
v___x_5957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5935_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set_uint8(v___x_5958_, sizeof(void*)*1, v___x_5914_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5955_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5959_);
lean_ctor_set(v___x_5960_, 1, v___x_5917_);
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set(v___x_5961_, 1, v___x_5919_);
v___x_5962_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5961_);
lean_ctor_set(v___x_5963_, 1, v___x_5962_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5963_);
lean_ctor_set(v___x_5964_, 1, v___x_5908_);
v___x_5965_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5966_ = l_Bool_repr___redArg(v_zeta_5881_);
v___x_5967_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5965_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
v___x_5968_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5968_, 0, v___x_5967_);
lean_ctor_set_uint8(v___x_5968_, sizeof(void*)*1, v___x_5914_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5964_);
lean_ctor_set(v___x_5969_, 1, v___x_5968_);
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
lean_ctor_set(v___x_5970_, 1, v___x_5917_);
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
lean_ctor_set(v___x_5971_, 1, v___x_5919_);
v___x_5972_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5971_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5973_);
lean_ctor_set(v___x_5974_, 1, v___x_5908_);
v___x_5975_ = l_Bool_repr___redArg(v_beta_5882_);
v___x_5976_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5965_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
lean_ctor_set_uint8(v___x_5977_, sizeof(void*)*1, v___x_5914_);
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5974_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5917_);
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set(v___x_5980_, 1, v___x_5919_);
v___x_5981_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5980_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
lean_ctor_set(v___x_5983_, 1, v___x_5908_);
v___x_5984_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5985_ = l_Bool_repr___redArg(v_eta_5883_);
v___x_5986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5984_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
v___x_5987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set_uint8(v___x_5987_, sizeof(void*)*1, v___x_5914_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5983_);
lean_ctor_set(v___x_5988_, 1, v___x_5987_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5988_);
lean_ctor_set(v___x_5989_, 1, v___x_5917_);
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
lean_ctor_set(v___x_5990_, 1, v___x_5919_);
v___x_5991_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5990_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set(v___x_5993_, 1, v___x_5908_);
v___x_5994_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5995_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5884_, v___x_5936_);
v___x_5996_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5994_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set_uint8(v___x_5997_, sizeof(void*)*1, v___x_5914_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5993_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
lean_ctor_set(v___x_5999_, 1, v___x_5917_);
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set(v___x_6000_, 1, v___x_5919_);
v___x_6001_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6000_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v___x_5908_);
v___x_6004_ = l_Bool_repr___redArg(v_iota_5885_);
v___x_6005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_5965_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v___x_6006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*1, v___x_5914_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6003_);
lean_ctor_set(v___x_6007_, 1, v___x_6006_);
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6007_);
lean_ctor_set(v___x_6008_, 1, v___x_5917_);
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6008_);
lean_ctor_set(v___x_6009_, 1, v___x_5919_);
v___x_6010_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6009_);
lean_ctor_set(v___x_6011_, 1, v___x_6010_);
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6011_);
lean_ctor_set(v___x_6012_, 1, v___x_5908_);
v___x_6013_ = l_Bool_repr___redArg(v_proj_5886_);
v___x_6014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_5965_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set_uint8(v___x_6015_, sizeof(void*)*1, v___x_5914_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6012_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5917_);
v___x_6018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6017_);
lean_ctor_set(v___x_6018_, 1, v___x_5919_);
v___x_6019_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6018_);
lean_ctor_set(v___x_6020_, 1, v___x_6019_);
v___x_6021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set(v___x_6021_, 1, v___x_5908_);
v___x_6022_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6023_ = l_Bool_repr___redArg(v_decide_5887_);
v___x_6024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6022_);
lean_ctor_set(v___x_6024_, 1, v___x_6023_);
v___x_6025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set_uint8(v___x_6025_, sizeof(void*)*1, v___x_5914_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6021_);
lean_ctor_set(v___x_6026_, 1, v___x_6025_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_5917_);
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set(v___x_6028_, 1, v___x_5919_);
v___x_6029_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6028_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set(v___x_6031_, 1, v___x_5908_);
v___x_6032_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6033_ = l_Bool_repr___redArg(v_arith_5888_);
v___x_6034_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6032_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set_uint8(v___x_6035_, sizeof(void*)*1, v___x_5914_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6031_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
lean_ctor_set(v___x_6037_, 1, v___x_5917_);
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_5919_);
v___x_6039_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6038_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_5908_);
v___x_6042_ = l_Bool_repr___redArg(v_autoUnfold_5889_);
v___x_6043_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_5935_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set_uint8(v___x_6044_, sizeof(void*)*1, v___x_5914_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6041_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6045_);
lean_ctor_set(v___x_6046_, 1, v___x_5917_);
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6046_);
lean_ctor_set(v___x_6047_, 1, v___x_5919_);
v___x_6048_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6047_);
lean_ctor_set(v___x_6049_, 1, v___x_6048_);
v___x_6050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
lean_ctor_set(v___x_6050_, 1, v___x_5908_);
v___x_6051_ = l_Bool_repr___redArg(v_dsimp_5890_);
v___x_6052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6032_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set_uint8(v___x_6053_, sizeof(void*)*1, v___x_5914_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6050_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_5917_);
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6055_);
lean_ctor_set(v___x_6056_, 1, v___x_5919_);
v___x_6057_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6056_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set(v___x_6059_, 1, v___x_5908_);
v___x_6060_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6061_ = l_Bool_repr___redArg(v_failIfUnchanged_5891_);
v___x_6062_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6060_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set_uint8(v___x_6063_, sizeof(void*)*1, v___x_5914_);
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6059_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
lean_ctor_set(v___x_6065_, 1, v___x_5917_);
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
lean_ctor_set(v___x_6066_, 1, v___x_5919_);
v___x_6067_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6066_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set(v___x_6069_, 1, v___x_5908_);
v___x_6070_ = l_Bool_repr___redArg(v_ground_5892_);
v___x_6071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6022_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set_uint8(v___x_6072_, sizeof(void*)*1, v___x_5914_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6069_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
lean_ctor_set(v___x_6074_, 1, v___x_5917_);
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set(v___x_6075_, 1, v___x_5919_);
v___x_6076_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6075_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
lean_ctor_set(v___x_6078_, 1, v___x_5908_);
v___x_6079_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6080_ = l_Bool_repr___redArg(v_unfoldPartialApp_5893_);
v___x_6081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6079_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set_uint8(v___x_6082_, sizeof(void*)*1, v___x_5914_);
v___x_6083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6078_);
lean_ctor_set(v___x_6083_, 1, v___x_6082_);
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6083_);
lean_ctor_set(v___x_6084_, 1, v___x_5917_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5919_);
v___x_6086_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6085_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set(v___x_6088_, 1, v___x_5908_);
v___x_6089_ = l_Bool_repr___redArg(v_zetaDelta_5894_);
v___x_6090_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_5994_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
v___x_6091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set_uint8(v___x_6091_, sizeof(void*)*1, v___x_5914_);
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6088_);
lean_ctor_set(v___x_6092_, 1, v___x_6091_);
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set(v___x_6093_, 1, v___x_5917_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set(v___x_6094_, 1, v___x_5919_);
v___x_6095_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6094_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6096_);
lean_ctor_set(v___x_6097_, 1, v___x_5908_);
v___x_6098_ = l_Bool_repr___redArg(v_index_5895_);
v___x_6099_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6032_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set_uint8(v___x_6100_, sizeof(void*)*1, v___x_5914_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6097_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_5917_);
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
lean_ctor_set(v___x_6103_, 1, v___x_5919_);
v___x_6104_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6103_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
v___x_6106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set(v___x_6106_, 1, v___x_5908_);
v___x_6107_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6108_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5896_);
v___x_6109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6107_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
v___x_6110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set_uint8(v___x_6110_, sizeof(void*)*1, v___x_5914_);
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6106_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6111_);
lean_ctor_set(v___x_6112_, 1, v___x_5917_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_5919_);
v___x_6114_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6113_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v___x_5908_);
v___x_6117_ = l_Bool_repr___redArg(v_zetaUnused_5897_);
v___x_6118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_5935_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set_uint8(v___x_6119_, sizeof(void*)*1, v___x_5914_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6116_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set(v___x_6121_, 1, v___x_5917_);
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set(v___x_6122_, 1, v___x_5919_);
v___x_6123_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6122_);
lean_ctor_set(v___x_6124_, 1, v___x_6123_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6124_);
lean_ctor_set(v___x_6125_, 1, v___x_5908_);
v___x_6126_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6127_ = l_Bool_repr___redArg(v_catchRuntime_5898_);
v___x_6128_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6126_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set_uint8(v___x_6129_, sizeof(void*)*1, v___x_5914_);
v___x_6130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6125_);
lean_ctor_set(v___x_6130_, 1, v___x_6129_);
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6130_);
lean_ctor_set(v___x_6131_, 1, v___x_5917_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5919_);
v___x_6133_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6132_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set(v___x_6135_, 1, v___x_5908_);
v___x_6136_ = l_Bool_repr___redArg(v_zetaHave_5899_);
v___x_6137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_5910_);
lean_ctor_set(v___x_6137_, 1, v___x_6136_);
v___x_6138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*1, v___x_5914_);
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6135_);
lean_ctor_set(v___x_6139_, 1, v___x_6138_);
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
lean_ctor_set(v___x_6140_, 1, v___x_5917_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6140_);
lean_ctor_set(v___x_6141_, 1, v___x_5919_);
v___x_6142_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6141_);
lean_ctor_set(v___x_6143_, 1, v___x_6142_);
v___x_6144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6143_);
lean_ctor_set(v___x_6144_, 1, v___x_5908_);
v___x_6145_ = l_Bool_repr___redArg(v_letToHave_5900_);
v___x_6146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_5994_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set_uint8(v___x_6147_, sizeof(void*)*1, v___x_5914_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6144_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
v___x_6149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set(v___x_6149_, 1, v___x_5917_);
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
lean_ctor_set(v___x_6150_, 1, v___x_5919_);
v___x_6151_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6150_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
v___x_6153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6152_);
lean_ctor_set(v___x_6153_, 1, v___x_5908_);
v___x_6154_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6155_ = l_Bool_repr___redArg(v_congrConsts_5901_);
v___x_6156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6154_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*1, v___x_5914_);
v___x_6158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6153_);
lean_ctor_set(v___x_6158_, 1, v___x_6157_);
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6158_);
lean_ctor_set(v___x_6159_, 1, v___x_5917_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set(v___x_6160_, 1, v___x_5919_);
v___x_6161_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6160_);
lean_ctor_set(v___x_6162_, 1, v___x_6161_);
v___x_6163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6162_);
lean_ctor_set(v___x_6163_, 1, v___x_5908_);
v___x_6164_ = l_Bool_repr___redArg(v_bitVecOfNat_5902_);
v___x_6165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6154_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set_uint8(v___x_6166_, sizeof(void*)*1, v___x_5914_);
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6163_);
lean_ctor_set(v___x_6167_, 1, v___x_6166_);
v___x_6168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6167_);
lean_ctor_set(v___x_6168_, 1, v___x_5917_);
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
lean_ctor_set(v___x_6169_, 1, v___x_5919_);
v___x_6170_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6169_);
lean_ctor_set(v___x_6171_, 1, v___x_6170_);
v___x_6172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6171_);
lean_ctor_set(v___x_6172_, 1, v___x_5908_);
v___x_6173_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6174_ = l_Bool_repr___redArg(v_warnExponents_5903_);
v___x_6175_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6173_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
v___x_6176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set_uint8(v___x_6176_, sizeof(void*)*1, v___x_5914_);
v___x_6177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6172_);
lean_ctor_set(v___x_6177_, 1, v___x_6176_);
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6177_);
lean_ctor_set(v___x_6178_, 1, v___x_5917_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_5919_);
v___x_6180_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6179_);
lean_ctor_set(v___x_6181_, 1, v___x_6180_);
v___x_6182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6181_);
lean_ctor_set(v___x_6182_, 1, v___x_5908_);
v___x_6183_ = l_Bool_repr___redArg(v_suggestions_5904_);
v___x_6184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6154_);
lean_ctor_set(v___x_6184_, 1, v___x_6183_);
v___x_6185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set_uint8(v___x_6185_, sizeof(void*)*1, v___x_5914_);
v___x_6186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6182_);
lean_ctor_set(v___x_6186_, 1, v___x_6185_);
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___x_5917_);
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
lean_ctor_set(v___x_6188_, 1, v___x_5919_);
v___x_6189_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6188_);
lean_ctor_set(v___x_6190_, 1, v___x_6189_);
v___x_6191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6190_);
lean_ctor_set(v___x_6191_, 1, v___x_5908_);
v___x_6192_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6193_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5905_, v___x_5936_);
v___x_6194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6192_);
lean_ctor_set(v___x_6194_, 1, v___x_6193_);
v___x_6195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6195_, 0, v___x_6194_);
lean_ctor_set_uint8(v___x_6195_, sizeof(void*)*1, v___x_5914_);
v___x_6196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6191_);
lean_ctor_set(v___x_6196_, 1, v___x_6195_);
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6196_);
lean_ctor_set(v___x_6197_, 1, v___x_5917_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___x_5919_);
v___x_6199_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6198_);
lean_ctor_set(v___x_6200_, 1, v___x_6199_);
v___x_6201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6200_);
lean_ctor_set(v___x_6201_, 1, v___x_5908_);
v___x_6202_ = l_Bool_repr___redArg(v_locals_5906_);
v___x_6203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6022_);
lean_ctor_set(v___x_6203_, 1, v___x_6202_);
v___x_6204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6204_, 0, v___x_6203_);
lean_ctor_set_uint8(v___x_6204_, sizeof(void*)*1, v___x_5914_);
v___x_6205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6205_, 0, v___x_6201_);
lean_ctor_set(v___x_6205_, 1, v___x_6204_);
v___x_6206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6205_);
lean_ctor_set(v___x_6206_, 1, v___x_5917_);
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
lean_ctor_set(v___x_6207_, 1, v___x_5919_);
v___x_6208_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6207_);
lean_ctor_set(v___x_6209_, 1, v___x_6208_);
v___x_6210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6209_);
lean_ctor_set(v___x_6210_, 1, v___x_5908_);
v___x_6211_ = l_Bool_repr___redArg(v_instances_5907_);
v___x_6212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_5994_);
lean_ctor_set(v___x_6212_, 1, v___x_6211_);
v___x_6213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6213_, 0, v___x_6212_);
lean_ctor_set_uint8(v___x_6213_, sizeof(void*)*1, v___x_5914_);
v___x_6214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6210_);
lean_ctor_set(v___x_6214_, 1, v___x_6213_);
v___x_6215_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6216_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
lean_ctor_set(v___x_6217_, 1, v___x_6214_);
v___x_6218_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6217_);
lean_ctor_set(v___x_6219_, 1, v___x_6218_);
v___x_6220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6220_, 0, v___x_6215_);
lean_ctor_set(v___x_6220_, 1, v___x_6219_);
v___x_6221_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6221_, 0, v___x_6220_);
lean_ctor_set_uint8(v___x_6221_, sizeof(void*)*1, v___x_5914_);
return v___x_6221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6222_, lean_object* v_prec_6223_){
_start:
{
lean_object* v___x_6224_; 
v___x_6224_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6222_);
return v___x_6224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6225_, lean_object* v_prec_6226_){
_start:
{
lean_object* v_res_6227_; 
v_res_6227_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6225_, v_prec_6226_);
lean_dec(v_prec_6226_);
return v_res_6227_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6230_, lean_object* v_x_6231_){
_start:
{
if (lean_obj_tag(v_x_6231_) == 0)
{
uint8_t v___x_6232_; 
v___x_6232_ = 0;
return v___x_6232_;
}
else
{
lean_object* v_head_6233_; lean_object* v_tail_6234_; uint8_t v___x_6235_; 
v_head_6233_ = lean_ctor_get(v_x_6231_, 0);
v_tail_6234_ = lean_ctor_get(v_x_6231_, 1);
v___x_6235_ = lean_nat_dec_eq(v_a_6230_, v_head_6233_);
if (v___x_6235_ == 0)
{
v_x_6231_ = v_tail_6234_;
goto _start;
}
else
{
return v___x_6235_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6237_, lean_object* v_x_6238_){
_start:
{
uint8_t v_res_6239_; lean_object* v_r_6240_; 
v_res_6239_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6237_, v_x_6238_);
lean_dec(v_x_6238_);
lean_dec(v_a_6237_);
v_r_6240_ = lean_box(v_res_6239_);
return v_r_6240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6241_, lean_object* v_x_6242_){
_start:
{
switch(lean_obj_tag(v_x_6241_))
{
case 0:
{
uint8_t v___x_6243_; 
v___x_6243_ = 1;
return v___x_6243_;
}
case 1:
{
lean_object* v_idxs_6244_; uint8_t v___x_6245_; 
v_idxs_6244_ = lean_ctor_get(v_x_6241_, 0);
v___x_6245_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6242_, v_idxs_6244_);
return v___x_6245_;
}
default: 
{
lean_object* v_idxs_6246_; uint8_t v___x_6247_; 
v_idxs_6246_ = lean_ctor_get(v_x_6241_, 0);
v___x_6247_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6242_, v_idxs_6246_);
if (v___x_6247_ == 0)
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6250_, lean_object* v_x_6251_){
_start:
{
uint8_t v_res_6252_; lean_object* v_r_6253_; 
v_res_6252_ = l_Lean_Meta_Occurrences_contains(v_x_6250_, v_x_6251_);
lean_dec(v_x_6251_);
lean_dec(v_x_6250_);
v_r_6253_ = lean_box(v_res_6252_);
return v_r_6253_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6254_){
_start:
{
if (lean_obj_tag(v_x_6254_) == 0)
{
uint8_t v___x_6255_; 
v___x_6255_ = 1;
return v___x_6255_;
}
else
{
uint8_t v___x_6256_; 
v___x_6256_ = 0;
return v___x_6256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6257_){
_start:
{
uint8_t v_res_6258_; lean_object* v_r_6259_; 
v_res_6258_ = l_Lean_Meta_Occurrences_isAll(v_x_6257_);
lean_dec(v_x_6257_);
v_r_6259_ = lean_box(v_res_6258_);
return v_r_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6260_){
_start:
{
switch(v_x_6260_)
{
case 0:
{
lean_object* v___x_6261_; 
v___x_6261_ = lean_unsigned_to_nat(0u);
return v___x_6261_;
}
case 1:
{
lean_object* v___x_6262_; 
v___x_6262_ = lean_unsigned_to_nat(1u);
return v___x_6262_;
}
default: 
{
lean_object* v___x_6263_; 
v___x_6263_ = lean_unsigned_to_nat(2u);
return v___x_6263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6264_){
_start:
{
uint8_t v_x_boxed_6265_; lean_object* v_res_6266_; 
v_x_boxed_6265_ = lean_unbox(v_x_6264_);
v_res_6266_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6265_);
return v_res_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6267_){
_start:
{
lean_inc(v_k_6267_);
return v_k_6267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6268_){
_start:
{
lean_object* v_res_6269_; 
v_res_6269_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6268_);
lean_dec(v_k_6268_);
return v_res_6269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6270_, lean_object* v_ctorIdx_6271_, uint8_t v_t_6272_, lean_object* v_h_6273_, lean_object* v_k_6274_){
_start:
{
lean_inc(v_k_6274_);
return v_k_6274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6275_, lean_object* v_ctorIdx_6276_, lean_object* v_t_6277_, lean_object* v_h_6278_, lean_object* v_k_6279_){
_start:
{
uint8_t v_t_boxed_6280_; lean_object* v_res_6281_; 
v_t_boxed_6280_ = lean_unbox(v_t_6277_);
v_res_6281_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6275_, v_ctorIdx_6276_, v_t_boxed_6280_, v_h_6278_, v_k_6279_);
lean_dec(v_k_6279_);
lean_dec(v_ctorIdx_6276_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6282_){
_start:
{
lean_inc(v_nonDependentFirst_6282_);
return v_nonDependentFirst_6282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6283_){
_start:
{
lean_object* v_res_6284_; 
v_res_6284_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6283_);
lean_dec(v_nonDependentFirst_6283_);
return v_res_6284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6285_, uint8_t v_t_6286_, lean_object* v_h_6287_, lean_object* v_nonDependentFirst_6288_){
_start:
{
lean_inc(v_nonDependentFirst_6288_);
return v_nonDependentFirst_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6289_, lean_object* v_t_6290_, lean_object* v_h_6291_, lean_object* v_nonDependentFirst_6292_){
_start:
{
uint8_t v_t_boxed_6293_; lean_object* v_res_6294_; 
v_t_boxed_6293_ = lean_unbox(v_t_6290_);
v_res_6294_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6289_, v_t_boxed_6293_, v_h_6291_, v_nonDependentFirst_6292_);
lean_dec(v_nonDependentFirst_6292_);
return v_res_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6295_){
_start:
{
lean_inc(v_nonDependentOnly_6295_);
return v_nonDependentOnly_6295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6296_){
_start:
{
lean_object* v_res_6297_; 
v_res_6297_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6296_);
lean_dec(v_nonDependentOnly_6296_);
return v_res_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6298_, uint8_t v_t_6299_, lean_object* v_h_6300_, lean_object* v_nonDependentOnly_6301_){
_start:
{
lean_inc(v_nonDependentOnly_6301_);
return v_nonDependentOnly_6301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6302_, lean_object* v_t_6303_, lean_object* v_h_6304_, lean_object* v_nonDependentOnly_6305_){
_start:
{
uint8_t v_t_boxed_6306_; lean_object* v_res_6307_; 
v_t_boxed_6306_ = lean_unbox(v_t_6303_);
v_res_6307_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6302_, v_t_boxed_6306_, v_h_6304_, v_nonDependentOnly_6305_);
lean_dec(v_nonDependentOnly_6305_);
return v_res_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6308_){
_start:
{
lean_inc(v_all_6308_);
return v_all_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6309_){
_start:
{
lean_object* v_res_6310_; 
v_res_6310_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6309_);
lean_dec(v_all_6309_);
return v_res_6310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6311_, uint8_t v_t_6312_, lean_object* v_h_6313_, lean_object* v_all_6314_){
_start:
{
lean_inc(v_all_6314_);
return v_all_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6315_, lean_object* v_t_6316_, lean_object* v_h_6317_, lean_object* v_all_6318_){
_start:
{
uint8_t v_t_boxed_6319_; lean_object* v_res_6320_; 
v_t_boxed_6319_ = lean_unbox(v_t_6316_);
v_res_6320_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6315_, v_t_boxed_6319_, v_h_6317_, v_all_6318_);
lean_dec(v_all_6318_);
return v_res_6320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6334_){
_start:
{
lean_object* v___x_6335_; uint8_t v___x_6336_; 
v___x_6335_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6334_);
v___x_6336_ = l_Lean_Syntax_isOfKind(v_c_6334_, v___x_6335_);
if (v___x_6336_ == 0)
{
lean_object* v___x_6337_; uint8_t v___x_6338_; 
v___x_6337_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6334_);
v___x_6338_ = l_Lean_Syntax_isOfKind(v_c_6334_, v___x_6337_);
if (v___x_6338_ == 0)
{
lean_object* v___x_6339_; uint8_t v___x_6340_; 
v___x_6339_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6334_);
v___x_6340_ = l_Lean_Syntax_isOfKind(v_c_6334_, v___x_6339_);
if (v___x_6340_ == 0)
{
lean_object* v___x_6341_; 
lean_dec(v_c_6334_);
v___x_6341_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6341_;
}
else
{
lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6342_ = lean_unsigned_to_nat(1u);
v___x_6343_ = lean_mk_empty_array_with_capacity(v___x_6342_);
v___x_6344_ = lean_array_push(v___x_6343_, v_c_6334_);
return v___x_6344_;
}
}
else
{
lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6345_ = lean_unsigned_to_nat(0u);
v___x_6346_ = l_Lean_Syntax_getArg(v_c_6334_, v___x_6345_);
lean_dec(v_c_6334_);
v___x_6347_ = l_Lean_Syntax_getArgs(v___x_6346_);
lean_dec(v___x_6346_);
return v___x_6347_;
}
}
else
{
lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; uint8_t v___x_6352_; 
v___x_6348_ = l_Lean_Syntax_getArgs(v_c_6334_);
lean_dec(v_c_6334_);
v___x_6349_ = lean_unsigned_to_nat(0u);
v___x_6350_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6351_ = lean_array_get_size(v___x_6348_);
v___x_6352_ = lean_nat_dec_lt(v___x_6349_, v___x_6351_);
if (v___x_6352_ == 0)
{
lean_dec_ref(v___x_6348_);
return v___x_6350_;
}
else
{
size_t v___x_6353_; size_t v___x_6354_; lean_object* v___x_6355_; 
v___x_6353_ = ((size_t)0ULL);
v___x_6354_ = lean_usize_of_nat(v___x_6351_);
v___x_6355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6348_, v___x_6353_, v___x_6354_, v___x_6350_);
lean_dec_ref(v___x_6348_);
return v___x_6355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6356_, size_t v_i_6357_, size_t v_stop_6358_, lean_object* v_b_6359_){
_start:
{
uint8_t v___x_6360_; 
v___x_6360_ = lean_usize_dec_eq(v_i_6357_, v_stop_6358_);
if (v___x_6360_ == 0)
{
lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; size_t v___x_6364_; size_t v___x_6365_; 
v___x_6361_ = lean_array_uget_borrowed(v_as_6356_, v_i_6357_);
lean_inc(v___x_6361_);
v___x_6362_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6361_);
v___x_6363_ = l_Array_append___redArg(v_b_6359_, v___x_6362_);
lean_dec_ref(v___x_6362_);
v___x_6364_ = ((size_t)1ULL);
v___x_6365_ = lean_usize_add(v_i_6357_, v___x_6364_);
v_i_6357_ = v___x_6365_;
v_b_6359_ = v___x_6363_;
goto _start;
}
else
{
return v_b_6359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6367_, lean_object* v_i_6368_, lean_object* v_stop_6369_, lean_object* v_b_6370_){
_start:
{
size_t v_i_boxed_6371_; size_t v_stop_boxed_6372_; lean_object* v_res_6373_; 
v_i_boxed_6371_ = lean_unbox_usize(v_i_6368_);
lean_dec(v_i_6368_);
v_stop_boxed_6372_ = lean_unbox_usize(v_stop_6369_);
lean_dec(v_stop_6369_);
v_res_6373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6367_, v_i_boxed_6371_, v_stop_boxed_6372_, v_b_6370_);
lean_dec_ref(v_as_6367_);
return v_res_6373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6374_){
_start:
{
lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; 
v___x_6375_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6376_ = lean_box(2);
v___x_6377_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6378_, 0, v___x_6376_);
lean_ctor_set(v___x_6378_, 1, v___x_6377_);
lean_ctor_set(v___x_6378_, 2, v_items_6374_);
v___x_6379_ = l_Lean_Syntax_node1(v___x_6376_, v___x_6375_, v___x_6378_);
return v___x_6379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6380_, lean_object* v_cfg_x27_6381_){
_start:
{
lean_object* v___x_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; 
v___x_6382_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6380_);
v___x_6383_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6381_);
v___x_6384_ = l_Array_append___redArg(v___x_6382_, v___x_6383_);
lean_dec_ref(v___x_6383_);
v___x_6385_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6384_);
return v___x_6385_;
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
