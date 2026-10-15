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
uint8_t v___y_572_; uint32_t v___y_583_; uint32_t v___y_588_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_string_utf8_byte_size(v_s_560_);
v___x_605_ = lean_nat_dec_lt(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_606_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_607_ = lean_string_append(v___x_606_, v_s_560_);
lean_dec_ref(v_s_560_);
v___x_608_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_609_ = lean_string_append(v___x_607_, v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
if (v_force_561_ == 0)
{
uint8_t v_c_611_; uint8_t v___x_620_; uint8_t v___x_621_; 
v_c_611_ = lean_string_get_byte_fast(v_s_560_, v___x_603_);
v___x_620_ = 97;
v___x_621_ = lean_uint8_dec_le(v___x_620_, v_c_611_);
if (v___x_621_ == 0)
{
goto v___jp_615_;
}
else
{
uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 122;
v___x_623_ = lean_uint8_dec_le(v_c_611_, v___x_622_);
if (v___x_623_ == 0)
{
goto v___jp_615_;
}
else
{
goto v___jp_600_;
}
}
v___jp_612_:
{
uint8_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 95;
v___x_614_ = lean_uint8_dec_eq(v_c_611_, v___x_613_);
if (v___x_614_ == 0)
{
goto v___jp_593_;
}
else
{
goto v___jp_600_;
}
}
v___jp_615_:
{
uint8_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 65;
v___x_617_ = lean_uint8_dec_le(v___x_616_, v_c_611_);
if (v___x_617_ == 0)
{
goto v___jp_612_;
}
else
{
uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 90;
v___x_619_ = lean_uint8_dec_le(v_c_611_, v___x_618_);
if (v___x_619_ == 0)
{
goto v___jp_612_;
}
else
{
goto v___jp_600_;
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
if (v___y_572_ == 0)
{
goto v___jp_562_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_s_560_);
return v___x_573_;
}
}
v___jp_574_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_string_utf8_byte_size(v_s_560_);
lean_inc_ref(v_s_560_);
v___x_577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_577_, 0, v_s_560_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
lean_ctor_set(v___x_577_, 2, v___x_576_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_substring_drop(v___x_577_, v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_581_ = lean_substring_all(v___x_579_, v___x_580_);
v___y_572_ = v___x_581_;
goto v___jp_571_;
}
v___jp_582_:
{
uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 95;
v___x_585_ = lean_uint32_dec_eq(v___y_583_, v___x_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
v___x_586_ = l_Lean_isLetterLike(v___y_583_);
if (v___x_586_ == 0)
{
v___y_572_ = v___x_586_;
goto v___jp_571_;
}
else
{
goto v___jp_574_;
}
}
else
{
goto v___jp_574_;
}
}
v___jp_587_:
{
uint32_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = 97;
v___x_590_ = lean_uint32_dec_le(v___x_589_, v___y_588_);
if (v___x_590_ == 0)
{
v___y_583_ = v___y_588_;
goto v___jp_582_;
}
else
{
uint32_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 122;
v___x_592_ = lean_uint32_dec_le(v___y_588_, v___x_591_);
if (v___x_592_ == 0)
{
v___y_583_ = v___y_588_;
goto v___jp_582_;
}
else
{
goto v___jp_574_;
}
}
}
v___jp_593_:
{
lean_object* v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_string_utf8_get(v_s_560_, v___x_594_);
v___x_596_ = 65;
v___x_597_ = lean_uint32_dec_le(v___x_596_, v___x_595_);
if (v___x_597_ == 0)
{
v___y_588_ = v___x_595_;
goto v___jp_587_;
}
else
{
uint32_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 90;
v___x_599_ = lean_uint32_dec_le(v___x_595_, v___x_598_);
if (v___x_599_ == 0)
{
v___y_588_ = v___x_595_;
goto v___jp_587_;
}
else
{
goto v___jp_574_;
}
}
}
v___jp_600_:
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_560_, v___x_601_);
if (v___x_602_ == 0)
{
goto v___jp_593_;
}
else
{
v___y_572_ = v___x_602_;
goto v___jp_571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_624_, lean_object* v_force_625_){
_start:
{
uint8_t v_force_boxed_626_; lean_object* v_res_627_; 
v_force_boxed_626_ = lean_unbox(v_force_625_);
v_res_627_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_624_, v_force_boxed_626_);
return v_res_627_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_628_){
_start:
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 187;
v___x_630_ = lean_uint32_dec_eq(v___y_628_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_631_){
_start:
{
uint32_t v___y_272__boxed_632_; uint8_t v_res_633_; lean_object* v_r_634_; 
v___y_272__boxed_632_ = lean_unbox_uint32(v___y_631_);
lean_dec(v___y_631_);
v_res_633_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_272__boxed_632_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_635_){
_start:
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 65;
v___x_658_ = lean_uint32_dec_le(v___x_657_, v___y_635_);
if (v___x_658_ == 0)
{
goto v___jp_652_;
}
else
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 90;
v___x_660_ = lean_uint32_dec_le(v___y_635_, v___x_659_);
if (v___x_660_ == 0)
{
goto v___jp_652_;
}
else
{
return v___x_660_;
}
}
v___jp_636_:
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 95;
v___x_638_ = lean_uint32_dec_eq(v___y_635_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 39;
v___x_640_ = lean_uint32_dec_eq(v___y_635_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 33;
v___x_642_ = lean_uint32_dec_eq(v___y_635_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 63;
v___x_644_ = lean_uint32_dec_eq(v___y_635_, v___x_643_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
v___x_645_ = l_Lean_isLetterLike(v___y_635_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_isSubScriptAlnum(v___y_635_);
return v___x_646_;
}
else
{
return v___x_645_;
}
}
else
{
return v___x_644_;
}
}
else
{
return v___x_642_;
}
}
else
{
return v___x_640_;
}
}
else
{
return v___x_638_;
}
}
v___jp_647_:
{
uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 48;
v___x_649_ = lean_uint32_dec_le(v___x_648_, v___y_635_);
if (v___x_649_ == 0)
{
goto v___jp_636_;
}
else
{
uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 57;
v___x_651_ = lean_uint32_dec_le(v___y_635_, v___x_650_);
if (v___x_651_ == 0)
{
goto v___jp_636_;
}
else
{
return v___x_651_;
}
}
}
v___jp_652_:
{
uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 97;
v___x_654_ = lean_uint32_dec_le(v___x_653_, v___y_635_);
if (v___x_654_ == 0)
{
goto v___jp_647_;
}
else
{
uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 122;
v___x_656_ = lean_uint32_dec_le(v___y_635_, v___x_655_);
if (v___x_656_ == 0)
{
goto v___jp_647_;
}
else
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_661_){
_start:
{
uint32_t v___y_279__boxed_662_; uint8_t v_res_663_; lean_object* v_r_664_; 
v___y_279__boxed_662_ = lean_unbox_uint32(v___y_661_);
lean_dec(v___y_661_);
v_res_663_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_279__boxed_662_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_667_, lean_object* v_s_668_, uint8_t v_force_669_){
_start:
{
if (v_escape_667_ == 0)
{
return v_s_668_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_string_utf8_byte_size(v_s_668_);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_673_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_674_ = lean_string_append(v___x_673_, v_s_668_);
lean_dec_ref(v_s_668_);
v___x_675_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___f_677_; uint8_t v___y_685_; 
v___f_677_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_669_ == 0)
{
lean_object* v___f_686_; uint32_t v___y_693_; uint32_t v___y_698_; uint8_t v_c_712_; uint8_t v___x_721_; uint8_t v___x_722_; 
v___f_686_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_712_ = lean_string_get_byte_fast(v_s_668_, v___x_670_);
v___x_721_ = 97;
v___x_722_ = lean_uint8_dec_le(v___x_721_, v_c_712_);
if (v___x_722_ == 0)
{
goto v___jp_716_;
}
else
{
uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 122;
v___x_724_ = lean_uint8_dec_le(v_c_712_, v___x_723_);
if (v___x_724_ == 0)
{
goto v___jp_716_;
}
else
{
goto v___jp_709_;
}
}
v___jp_687_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
lean_inc_ref(v_s_668_);
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v_s_668_);
lean_ctor_set(v___x_688_, 1, v___x_670_);
lean_ctor_set(v___x_688_, 2, v___x_671_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_substring_drop(v___x_688_, v___x_689_);
v___x_691_ = lean_substring_all(v___x_690_, v___f_686_);
v___y_685_ = v___x_691_;
goto v___jp_684_;
}
v___jp_692_:
{
uint32_t v___x_694_; uint8_t v___x_695_; 
v___x_694_ = 95;
v___x_695_ = lean_uint32_dec_eq(v___y_693_, v___x_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; 
v___x_696_ = l_Lean_isLetterLike(v___y_693_);
if (v___x_696_ == 0)
{
v___y_685_ = v___x_696_;
goto v___jp_684_;
}
else
{
goto v___jp_687_;
}
}
else
{
goto v___jp_687_;
}
}
v___jp_697_:
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 97;
v___x_700_ = lean_uint32_dec_le(v___x_699_, v___y_698_);
if (v___x_700_ == 0)
{
v___y_693_ = v___y_698_;
goto v___jp_692_;
}
else
{
uint32_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = 122;
v___x_702_ = lean_uint32_dec_le(v___y_698_, v___x_701_);
if (v___x_702_ == 0)
{
v___y_693_ = v___y_698_;
goto v___jp_692_;
}
else
{
goto v___jp_687_;
}
}
}
v___jp_703_:
{
uint32_t v___x_704_; uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_string_utf8_get(v_s_668_, v___x_670_);
v___x_705_ = 65;
v___x_706_ = lean_uint32_dec_le(v___x_705_, v___x_704_);
if (v___x_706_ == 0)
{
v___y_698_ = v___x_704_;
goto v___jp_697_;
}
else
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 90;
v___x_708_ = lean_uint32_dec_le(v___x_704_, v___x_707_);
if (v___x_708_ == 0)
{
v___y_698_ = v___x_704_;
goto v___jp_697_;
}
else
{
goto v___jp_687_;
}
}
}
v___jp_709_:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_668_, v___x_710_);
if (v___x_711_ == 0)
{
goto v___jp_703_;
}
else
{
v___y_685_ = v___x_711_;
goto v___jp_684_;
}
}
v___jp_713_:
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 95;
v___x_715_ = lean_uint8_dec_eq(v_c_712_, v___x_714_);
if (v___x_715_ == 0)
{
goto v___jp_703_;
}
else
{
goto v___jp_709_;
}
}
v___jp_716_:
{
uint8_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 65;
v___x_718_ = lean_uint8_dec_le(v___x_717_, v_c_712_);
if (v___x_718_ == 0)
{
goto v___jp_713_;
}
else
{
uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 90;
v___x_720_ = lean_uint8_dec_le(v_c_712_, v___x_719_);
if (v___x_720_ == 0)
{
goto v___jp_713_;
}
else
{
goto v___jp_709_;
}
}
}
}
else
{
goto v___jp_678_;
}
v___jp_678_:
{
uint8_t v___x_679_; 
lean_inc_ref(v_s_668_);
v___x_679_ = lean_string_any(v_s_668_, v___f_677_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_680_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_681_ = lean_string_append(v___x_680_, v_s_668_);
lean_dec_ref(v_s_668_);
v___x_682_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_683_ = lean_string_append(v___x_681_, v___x_682_);
return v___x_683_;
}
else
{
return v_s_668_;
}
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
goto v___jp_678_;
}
else
{
return v_s_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_725_, lean_object* v_s_726_, lean_object* v_force_727_){
_start:
{
uint8_t v_escape_boxed_728_; uint8_t v_force_boxed_729_; lean_object* v_res_730_; 
v_escape_boxed_728_ = lean_unbox(v_escape_725_);
v_force_boxed_729_ = lean_unbox(v_force_727_);
v_res_730_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_728_, v_s_726_, v_force_boxed_729_);
return v_res_730_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = 0;
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_733_);
lean_dec_ref(v_x_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_738_, uint8_t v_escape_739_, lean_object* v_n_740_, lean_object* v_isToken_741_){
_start:
{
switch(lean_obj_tag(v_n_740_))
{
case 0:
{
lean_object* v___x_742_; 
lean_dec_ref(v_isToken_741_);
v___x_742_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_742_;
}
case 1:
{
lean_object* v_pre_743_; 
v_pre_743_ = lean_ctor_get(v_n_740_, 0);
if (lean_obj_tag(v_pre_743_) == 0)
{
lean_object* v_str_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; 
v_str_744_ = lean_ctor_get(v_n_740_, 1);
lean_inc_ref_n(v_str_744_, 2);
lean_dec_ref_known(v_n_740_, 2);
v___x_745_ = lean_apply_1(v_isToken_741_, v_str_744_);
v___x_746_ = lean_unbox(v___x_745_);
v___x_747_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_739_, v_str_744_, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v_str_748_; lean_object* v_r_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v_r_x27_753_; 
lean_inc(v_pre_743_);
v_str_748_ = lean_ctor_get(v_n_740_, 1);
lean_inc_ref_n(v_str_748_, 2);
lean_dec_ref_known(v_n_740_, 2);
lean_inc_ref(v_isToken_741_);
v_r_749_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_738_, v_escape_739_, v_pre_743_, v_isToken_741_);
v___x_750_ = lean_string_append(v_r_749_, v_sep_738_);
v___x_751_ = 0;
v___x_752_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_739_, v_str_748_, v___x_751_);
lean_inc_ref(v___x_750_);
v_r_x27_753_ = lean_string_append(v___x_750_, v___x_752_);
lean_dec_ref(v___x_752_);
if (v_escape_739_ == 0)
{
lean_dec_ref(v___x_750_);
lean_dec_ref(v_str_748_);
lean_dec_ref(v_isToken_741_);
return v_r_x27_753_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
lean_inc_ref(v_r_x27_753_);
v___x_754_ = lean_apply_1(v_isToken_741_, v_r_x27_753_);
v___x_755_ = lean_unbox(v___x_754_);
if (v___x_755_ == 0)
{
lean_dec_ref(v___x_750_);
lean_dec_ref(v_str_748_);
return v_r_x27_753_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref(v_r_x27_753_);
v___x_756_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_739_, v_str_748_, v_escape_739_);
v___x_757_ = lean_string_append(v___x_750_, v___x_756_);
lean_dec_ref(v___x_756_);
return v___x_757_;
}
}
}
}
default: 
{
lean_object* v_pre_758_; 
lean_dec_ref(v_isToken_741_);
v_pre_758_ = lean_ctor_get(v_n_740_, 0);
if (lean_obj_tag(v_pre_758_) == 0)
{
lean_object* v_i_759_; lean_object* v___x_760_; 
v_i_759_ = lean_ctor_get(v_n_740_, 1);
lean_inc(v_i_759_);
lean_dec_ref_known(v_n_740_, 2);
v___x_760_ = l_Nat_reprFast(v_i_759_);
return v___x_760_;
}
else
{
lean_object* v_i_761_; lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_inc(v_pre_758_);
v_i_761_ = lean_ctor_get(v_n_740_, 1);
lean_inc(v_i_761_);
lean_dec_ref_known(v_n_740_, 2);
v___f_762_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_763_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_738_, v_escape_739_, v_pre_758_, v___f_762_);
v___x_764_ = lean_string_append(v___x_763_, v_sep_738_);
v___x_765_ = l_Nat_reprFast(v_i_761_);
v___x_766_ = lean_string_append(v___x_764_, v___x_765_);
lean_dec_ref(v___x_765_);
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_767_, lean_object* v_escape_768_, lean_object* v_n_769_, lean_object* v_isToken_770_){
_start:
{
uint8_t v_escape_boxed_771_; lean_object* v_res_772_; 
v_escape_boxed_771_ = lean_unbox(v_escape_768_);
v_res_772_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_767_, v_escape_boxed_771_, v_n_769_, v_isToken_770_);
lean_dec_ref(v_sep_767_);
return v_res_772_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_778_){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; uint8_t v___x_781_; 
v___x_779_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_780_ = lean_name_eq(v_n_778_, v___x_779_);
v___x_781_ = 1;
if (v___x_780_ == 0)
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Name_getRoot(v_n_778_);
if (lean_obj_tag(v___x_782_) == 1)
{
lean_object* v_str_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_str_783_ = lean_ctor_get(v___x_782_, 1);
lean_inc_ref_n(v_str_783_, 2);
lean_dec_ref_known(v___x_782_, 2);
v___x_784_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_785_ = lean_string_isprefixof(v___x_784_, v_str_783_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_787_ = lean_string_isprefixof(v___x_786_, v_str_783_);
return v___x_787_;
}
else
{
lean_dec_ref(v_str_783_);
return v___x_781_;
}
}
else
{
lean_dec(v___x_782_);
return v___x_780_;
}
}
else
{
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_788_);
lean_dec(v_n_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_791_, uint8_t v_escape_792_, lean_object* v_isToken_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_792_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_794_, v_escape_792_, v_n_791_, v_isToken_793_);
return v___x_795_;
}
else
{
uint8_t v___x_796_; 
lean_inc(v_n_791_);
v___x_796_ = l_Lean_Name_isInaccessibleUserName(v_n_791_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; 
v___x_797_ = l_Lean_Name_hasMacroScopes(v_n_791_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; 
v___x_798_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_791_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_794_, v_escape_792_, v_n_791_, v_isToken_793_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_794_, v___x_797_, v_n_791_, v_isToken_793_);
return v___x_800_;
}
}
else
{
lean_object* v___x_801_; 
v___x_801_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_794_, v___x_796_, v_n_791_, v_isToken_793_);
return v___x_801_;
}
}
else
{
uint8_t v___x_802_; lean_object* v___x_803_; 
v___x_802_ = 0;
v___x_803_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_794_, v___x_802_, v_n_791_, v_isToken_793_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_804_, lean_object* v_escape_805_, lean_object* v_isToken_806_){
_start:
{
uint8_t v_escape_boxed_807_; lean_object* v_res_808_; 
v_escape_boxed_807_ = lean_unbox(v_escape_805_);
v_res_808_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_804_, v_escape_boxed_807_, v_isToken_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_809_, uint8_t v_escape_810_, lean_object* v_n_811_){
_start:
{
switch(lean_obj_tag(v_n_811_))
{
case 0:
{
lean_object* v___x_812_; 
v___x_812_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_812_;
}
case 1:
{
lean_object* v_pre_813_; 
v_pre_813_ = lean_ctor_get(v_n_811_, 0);
if (lean_obj_tag(v_pre_813_) == 0)
{
lean_object* v_str_814_; uint8_t v___x_815_; lean_object* v___x_816_; 
v_str_814_ = lean_ctor_get(v_n_811_, 1);
lean_inc_ref(v_str_814_);
lean_dec_ref_known(v_n_811_, 2);
v___x_815_ = 0;
v___x_816_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_810_, v_str_814_, v___x_815_);
return v___x_816_;
}
else
{
lean_object* v_str_817_; lean_object* v_r_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v_r_x27_822_; 
lean_inc(v_pre_813_);
v_str_817_ = lean_ctor_get(v_n_811_, 1);
lean_inc_ref(v_str_817_);
lean_dec_ref_known(v_n_811_, 2);
v_r_818_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_809_, v_escape_810_, v_pre_813_);
v___x_819_ = lean_string_append(v_r_818_, v_sep_809_);
v___x_820_ = 0;
v___x_821_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_810_, v_str_817_, v___x_820_);
v_r_x27_822_ = lean_string_append(v___x_819_, v___x_821_);
lean_dec_ref(v___x_821_);
return v_r_x27_822_;
}
}
default: 
{
lean_object* v_pre_823_; 
v_pre_823_ = lean_ctor_get(v_n_811_, 0);
if (lean_obj_tag(v_pre_823_) == 0)
{
lean_object* v_i_824_; lean_object* v___x_825_; 
v_i_824_ = lean_ctor_get(v_n_811_, 1);
lean_inc(v_i_824_);
lean_dec_ref_known(v_n_811_, 2);
v___x_825_ = l_Nat_reprFast(v_i_824_);
return v___x_825_;
}
else
{
lean_object* v_i_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc(v_pre_823_);
v_i_826_ = lean_ctor_get(v_n_811_, 1);
lean_inc(v_i_826_);
lean_dec_ref_known(v_n_811_, 2);
v___x_827_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_809_, v_escape_810_, v_pre_823_);
v___x_828_ = lean_string_append(v___x_827_, v_sep_809_);
v___x_829_ = l_Nat_reprFast(v_i_826_);
v___x_830_ = lean_string_append(v___x_828_, v___x_829_);
lean_dec_ref(v___x_829_);
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_831_, lean_object* v_escape_832_, lean_object* v_n_833_){
_start:
{
uint8_t v_escape_boxed_834_; lean_object* v_res_835_; 
v_escape_boxed_834_ = lean_unbox(v_escape_832_);
v_res_835_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_831_, v_escape_boxed_834_, v_n_833_);
lean_dec_ref(v_sep_831_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_836_, uint8_t v_escape_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_837_ == 0)
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_838_, v_escape_837_, v_n_836_);
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
lean_inc(v_n_836_);
v___x_840_ = l_Lean_Name_isInaccessibleUserName(v_n_836_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_Name_hasMacroScopes(v_n_836_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; 
v___x_842_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_836_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_838_, v_escape_837_, v_n_836_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_838_, v___x_841_, v_n_836_);
return v___x_844_;
}
}
else
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_838_, v___x_840_, v_n_836_);
return v___x_845_;
}
}
else
{
uint8_t v___x_846_; lean_object* v___x_847_; 
v___x_846_ = 0;
v___x_847_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_838_, v___x_846_, v_n_836_);
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_848_, lean_object* v_escape_849_){
_start:
{
uint8_t v_escape_boxed_850_; lean_object* v_res_851_; 
v_escape_boxed_850_ = lean_unbox(v_escape_849_);
v_res_851_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_848_, v_escape_boxed_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_852_, uint8_t v_escape_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_852_, v_escape_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_855_, lean_object* v_escape_856_){
_start:
{
uint8_t v_escape_boxed_857_; lean_object* v_res_858_; 
v_escape_boxed_857_ = lean_unbox(v_escape_856_);
v_res_858_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_855_, v_escape_boxed_857_);
return v_res_858_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_859_){
_start:
{
switch(lean_obj_tag(v_x_859_))
{
case 0:
{
uint8_t v___x_860_; 
v___x_860_ = 0;
return v___x_860_;
}
case 1:
{
lean_object* v_pre_861_; 
v_pre_861_ = lean_ctor_get(v_x_859_, 0);
v_x_859_ = v_pre_861_;
goto _start;
}
default: 
{
uint8_t v___x_863_; 
v___x_863_ = 1;
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_864_);
lean_dec(v_x_864_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_882_, lean_object* v_prec_883_){
_start:
{
switch(lean_obj_tag(v_n_882_))
{
case 0:
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_884_;
}
case 1:
{
lean_object* v_pre_885_; lean_object* v_str_886_; uint8_t v___x_887_; 
v_pre_885_ = lean_ctor_get(v_n_882_, 0);
v_str_886_ = lean_ctor_get(v_n_882_, 1);
v___x_887_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_885_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_888_ = 1;
v___x_889_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_890_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_882_, v___x_888_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_889_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc_ref(v_str_886_);
lean_inc(v_pre_885_);
lean_dec_ref_known(v_n_882_, 2);
v___x_893_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_894_ = lean_unsigned_to_nat(1024u);
v___x_895_ = l_Lean_Name_reprPrec(v_pre_885_, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_893_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_String_quote(v_str_886_);
v___x_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_898_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Repr_addAppParen(v___x_901_, v_prec_883_);
return v___x_902_;
}
}
default: 
{
lean_object* v_pre_903_; lean_object* v_i_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_pre_903_ = lean_ctor_get(v_n_882_, 0);
lean_inc(v_pre_903_);
v_i_904_ = lean_ctor_get(v_n_882_, 1);
lean_inc(v_i_904_);
lean_dec_ref_known(v_n_882_, 2);
v___x_905_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_906_ = lean_unsigned_to_nat(1024u);
v___x_907_ = l_Lean_Name_reprPrec(v_pre_903_, v___x_906_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_905_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Nat_reprFast(v_i_904_);
v___x_912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_910_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Repr_addAppParen(v___x_913_, v_prec_883_);
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_915_, lean_object* v_prec_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Name_reprPrec(v_n_915_, v_prec_916_);
lean_dec(v_prec_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 1)
{
lean_object* v_pre_921_; lean_object* v_str_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_pre_921_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_pre_921_);
v_str_922_ = lean_ctor_get(v_x_920_, 1);
lean_inc_ref(v_str_922_);
lean_dec_ref_known(v_x_920_, 2);
v___x_923_ = lean_string_capitalize(v_str_922_);
v___x_924_ = l_Lean_Name_str___override(v_pre_921_, v___x_923_);
return v___x_924_;
}
else
{
return v_x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
switch(lean_obj_tag(v_x_925_))
{
case 0:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_inc(v_x_927_);
return v_x_927_;
}
else
{
return v_x_925_;
}
}
case 1:
{
lean_object* v_pre_928_; lean_object* v_str_929_; uint8_t v___x_930_; 
v_pre_928_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_pre_928_);
v_str_929_ = lean_ctor_get(v_x_925_, 1);
lean_inc_ref(v_str_929_);
v___x_930_ = lean_name_eq(v_x_925_, v_x_926_);
lean_dec_ref_known(v_x_925_, 2);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Lean_Name_replacePrefix(v_pre_928_, v_x_926_, v_x_927_);
v___x_932_ = l_Lean_Name_str___override(v___x_931_, v_str_929_);
return v___x_932_;
}
else
{
lean_dec_ref(v_str_929_);
lean_dec(v_pre_928_);
lean_inc(v_x_927_);
return v_x_927_;
}
}
default: 
{
lean_object* v_pre_933_; lean_object* v_i_934_; uint8_t v___x_935_; 
v_pre_933_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_pre_933_);
v_i_934_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_i_934_);
v___x_935_ = lean_name_eq(v_x_925_, v_x_926_);
lean_dec_ref_known(v_x_925_, 2);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = l_Lean_Name_replacePrefix(v_pre_933_, v_x_926_, v_x_927_);
v___x_937_ = l_Lean_Name_num___override(v___x_936_, v_i_934_);
return v___x_937_;
}
else
{
lean_dec(v_i_934_);
lean_dec(v_pre_933_);
lean_inc(v_x_927_);
return v_x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Name_replacePrefix(v_x_938_, v_x_939_, v_x_940_);
lean_dec(v_x_940_);
lean_dec(v_x_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
switch(lean_obj_tag(v_x_943_))
{
case 0:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_x_942_);
return v___x_944_;
}
case 1:
{
if (lean_obj_tag(v_x_942_) == 1)
{
lean_object* v_pre_945_; lean_object* v_str_946_; lean_object* v_pre_947_; lean_object* v_str_948_; uint8_t v___x_949_; 
v_pre_945_ = lean_ctor_get(v_x_943_, 0);
v_str_946_ = lean_ctor_get(v_x_943_, 1);
v_pre_947_ = lean_ctor_get(v_x_942_, 0);
lean_inc(v_pre_947_);
v_str_948_ = lean_ctor_get(v_x_942_, 1);
lean_inc_ref(v_str_948_);
lean_dec_ref_known(v_x_942_, 2);
v___x_949_ = lean_string_dec_eq(v_str_948_, v_str_946_);
lean_dec_ref(v_str_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v_pre_947_);
v___x_950_ = lean_box(0);
return v___x_950_;
}
else
{
v_x_942_ = v_pre_947_;
v_x_943_ = v_pre_945_;
goto _start;
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v_x_942_);
v___x_952_ = lean_box(0);
return v___x_952_;
}
}
default: 
{
if (lean_obj_tag(v_x_942_) == 2)
{
lean_object* v_pre_953_; lean_object* v_i_954_; lean_object* v_pre_955_; lean_object* v_i_956_; uint8_t v___x_957_; 
v_pre_953_ = lean_ctor_get(v_x_943_, 0);
v_i_954_ = lean_ctor_get(v_x_943_, 1);
v_pre_955_ = lean_ctor_get(v_x_942_, 0);
lean_inc(v_pre_955_);
v_i_956_ = lean_ctor_get(v_x_942_, 1);
lean_inc(v_i_956_);
lean_dec_ref_known(v_x_942_, 2);
v___x_957_ = lean_nat_dec_eq(v_i_956_, v_i_954_);
lean_dec(v_i_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec(v_pre_955_);
v___x_958_ = lean_box(0);
return v___x_958_;
}
else
{
v_x_942_ = v_pre_955_;
v_x_943_ = v_pre_953_;
goto _start;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v_x_942_);
v___x_960_ = lean_box(0);
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Name_eraseSuffix_x3f(v_x_961_, v_x_962_);
lean_dec(v_x_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_964_, lean_object* v_f_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Name_hasMacroScopes(v_n_964_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = lean_apply_1(v_f_965_, v_n_964_);
return v___x_967_;
}
else
{
lean_object* v_view_968_; lean_object* v_name_969_; lean_object* v_imported_970_; lean_object* v_ctx_971_; lean_object* v_scopes_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_981_; 
v_view_968_ = l_Lean_extractMacroScopes(v_n_964_);
v_name_969_ = lean_ctor_get(v_view_968_, 0);
v_imported_970_ = lean_ctor_get(v_view_968_, 1);
v_ctx_971_ = lean_ctor_get(v_view_968_, 2);
v_scopes_972_ = lean_ctor_get(v_view_968_, 3);
v_isSharedCheck_981_ = !lean_is_exclusive(v_view_968_);
if (v_isSharedCheck_981_ == 0)
{
v___x_974_ = v_view_968_;
v_isShared_975_ = v_isSharedCheck_981_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_scopes_972_);
lean_inc(v_ctx_971_);
lean_inc(v_imported_970_);
lean_inc(v_name_969_);
lean_dec(v_view_968_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_981_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_apply_1(v_f_965_, v_name_969_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_imported_970_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_ctx_971_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_scopes_972_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_MacroScopesView_review(v___x_978_);
return v___x_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 1)
{
lean_object* v_pre_984_; lean_object* v_str_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_pre_984_ = lean_ctor_get(v_x_983_, 0);
lean_inc(v_pre_984_);
v_str_985_ = lean_ctor_get(v_x_983_, 1);
lean_inc_ref(v_str_985_);
lean_dec_ref_known(v_x_983_, 2);
v___x_986_ = lean_string_append(v_str_985_, v_suffix_982_);
lean_dec_ref(v_suffix_982_);
v___x_987_ = l_Lean_Name_str___override(v_pre_984_, v___x_986_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Name_str___override(v_x_983_, v_suffix_982_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_989_, lean_object* v_suffix_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_Name_hasMacroScopes(v_n_989_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Name_appendAfter___lam__0(v_suffix_990_, v_n_989_);
return v___x_992_;
}
else
{
lean_object* v_view_993_; lean_object* v_name_994_; lean_object* v_imported_995_; lean_object* v_ctx_996_; lean_object* v_scopes_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1006_; 
v_view_993_ = l_Lean_extractMacroScopes(v_n_989_);
v_name_994_ = lean_ctor_get(v_view_993_, 0);
v_imported_995_ = lean_ctor_get(v_view_993_, 1);
v_ctx_996_ = lean_ctor_get(v_view_993_, 2);
v_scopes_997_ = lean_ctor_get(v_view_993_, 3);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_view_993_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_999_ = v_view_993_;
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_scopes_997_);
lean_inc(v_ctx_996_);
lean_inc(v_imported_995_);
lean_inc(v_name_994_);
lean_dec(v_view_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = l_Lean_Name_appendAfter___lam__0(v_suffix_990_, v_name_994_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_imported_995_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_ctx_996_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_scopes_997_);
v___x_1003_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_MacroScopesView_review(v___x_1003_);
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 1)
{
lean_object* v_pre_1009_; lean_object* v_str_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_pre_1009_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_pre_1009_);
v_str_1010_ = lean_ctor_get(v_x_1008_, 1);
lean_inc_ref(v_str_1010_);
lean_dec_ref_known(v_x_1008_, 2);
v___x_1011_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1012_ = lean_string_append(v_str_1010_, v___x_1011_);
v___x_1013_ = l_Nat_reprFast(v_idx_1007_);
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = l_Lean_Name_str___override(v_pre_1009_, v___x_1014_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1016_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1017_ = l_Nat_reprFast(v_idx_1007_);
v___x_1018_ = lean_string_append(v___x_1016_, v___x_1017_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = l_Lean_Name_str___override(v_x_1008_, v___x_1018_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1020_, lean_object* v_idx_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = l_Lean_Name_hasMacroScopes(v_n_1020_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1021_, v_n_1020_);
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
v___x_1032_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1021_, v_name_1025_);
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
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1038_, lean_object* v_x_1039_){
_start:
{
switch(lean_obj_tag(v_x_1039_))
{
case 0:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Name_str___override(v_x_1039_, v_pre_1038_);
return v___x_1040_;
}
case 1:
{
lean_object* v_pre_1041_; lean_object* v_str_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v_pre_1041_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_pre_1041_);
v_str_1042_ = lean_ctor_get(v_x_1039_, 1);
lean_inc_ref(v_str_1042_);
lean_dec_ref_known(v_x_1039_, 2);
v___x_1043_ = lean_string_append(v_pre_1038_, v_str_1042_);
lean_dec_ref(v_str_1042_);
v___x_1044_ = l_Lean_Name_str___override(v_pre_1041_, v___x_1043_);
return v___x_1044_;
}
default: 
{
lean_object* v_pre_1045_; lean_object* v_i_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_pre_1045_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_pre_1045_);
v_i_1046_ = lean_ctor_get(v_x_1039_, 1);
lean_inc(v_i_1046_);
lean_dec_ref_known(v_x_1039_, 2);
v___x_1047_ = l_Lean_Name_str___override(v_pre_1045_, v_pre_1038_);
v___x_1048_ = l_Lean_Name_num___override(v___x_1047_, v_i_1046_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore(lean_object* v_n_1049_, lean_object* v_pre_1050_){
_start:
{
uint8_t v___x_1051_; 
v___x_1051_ = l_Lean_Name_hasMacroScopes(v_n_1049_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Name_appendBefore___lam__0(v_pre_1050_, v_n_1049_);
return v___x_1052_;
}
else
{
lean_object* v_view_1053_; lean_object* v_name_1054_; lean_object* v_imported_1055_; lean_object* v_ctx_1056_; lean_object* v_scopes_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1066_; 
v_view_1053_ = l_Lean_extractMacroScopes(v_n_1049_);
v_name_1054_ = lean_ctor_get(v_view_1053_, 0);
v_imported_1055_ = lean_ctor_get(v_view_1053_, 1);
v_ctx_1056_ = lean_ctor_get(v_view_1053_, 2);
v_scopes_1057_ = lean_ctor_get(v_view_1053_, 3);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_view_1053_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1059_ = v_view_1053_;
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_scopes_1057_);
lean_inc(v_ctx_1056_);
lean_inc(v_imported_1055_);
lean_inc(v_name_1054_);
lean_dec(v_view_1053_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = l_Lean_Name_appendBefore___lam__0(v_pre_1050_, v_name_1054_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_imported_1055_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_ctx_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_scopes_1057_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_MacroScopesView_review(v___x_1063_);
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_h__1_1069_, lean_object* v_h__2_1070_, lean_object* v_h__3_1071_, lean_object* v_h__4_1072_){
_start:
{
switch(lean_obj_tag(v_x_1067_))
{
case 0:
{
lean_dec(v_h__3_1071_);
lean_dec(v_h__2_1070_);
if (lean_obj_tag(v_x_1068_) == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_h__4_1072_);
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_apply_1(v_h__1_1069_, v___x_1073_);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; 
lean_dec(v_h__1_1069_);
v___x_1075_ = lean_apply_5(v_h__4_1072_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1075_;
}
}
case 1:
{
lean_dec(v_h__3_1071_);
lean_dec(v_h__1_1069_);
if (lean_obj_tag(v_x_1068_) == 1)
{
lean_object* v_pre_1076_; lean_object* v_str_1077_; lean_object* v_pre_1078_; lean_object* v_str_1079_; lean_object* v___x_1080_; 
lean_dec(v_h__4_1072_);
v_pre_1076_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_pre_1076_);
v_str_1077_ = lean_ctor_get(v_x_1067_, 1);
lean_inc_ref(v_str_1077_);
lean_dec_ref_known(v_x_1067_, 2);
v_pre_1078_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_pre_1078_);
v_str_1079_ = lean_ctor_get(v_x_1068_, 1);
lean_inc_ref(v_str_1079_);
lean_dec_ref_known(v_x_1068_, 2);
v___x_1080_ = lean_apply_4(v_h__2_1070_, v_pre_1076_, v_str_1077_, v_pre_1078_, v_str_1079_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; 
lean_dec(v_h__2_1070_);
v___x_1081_ = lean_apply_5(v_h__4_1072_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1081_;
}
}
default: 
{
lean_dec(v_h__2_1070_);
lean_dec(v_h__1_1069_);
if (lean_obj_tag(v_x_1068_) == 2)
{
lean_object* v_pre_1082_; lean_object* v_i_1083_; lean_object* v_pre_1084_; lean_object* v_i_1085_; lean_object* v___x_1086_; 
lean_dec(v_h__4_1072_);
v_pre_1082_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_pre_1082_);
v_i_1083_ = lean_ctor_get(v_x_1067_, 1);
lean_inc(v_i_1083_);
lean_dec_ref_known(v_x_1067_, 2);
v_pre_1084_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_pre_1084_);
v_i_1085_ = lean_ctor_get(v_x_1068_, 1);
lean_inc(v_i_1085_);
lean_dec_ref_known(v_x_1068_, 2);
v___x_1086_ = lean_apply_4(v_h__3_1071_, v_pre_1082_, v_i_1083_, v_pre_1084_, v_i_1085_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
lean_dec(v_h__3_1071_);
v___x_1087_ = lean_apply_5(v_h__4_1072_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_h__1_1091_, lean_object* v_h__2_1092_, lean_object* v_h__3_1093_, lean_object* v_h__4_1094_){
_start:
{
switch(lean_obj_tag(v_x_1089_))
{
case 0:
{
lean_dec(v_h__3_1093_);
lean_dec(v_h__2_1092_);
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__4_1094_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_apply_1(v_h__1_1091_, v___x_1095_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; 
lean_dec(v_h__1_1091_);
v___x_1097_ = lean_apply_5(v_h__4_1094_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1097_;
}
}
case 1:
{
lean_dec(v_h__3_1093_);
lean_dec(v_h__1_1091_);
if (lean_obj_tag(v_x_1090_) == 1)
{
lean_object* v_pre_1098_; lean_object* v_str_1099_; lean_object* v_pre_1100_; lean_object* v_str_1101_; lean_object* v___x_1102_; 
lean_dec(v_h__4_1094_);
v_pre_1098_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_pre_1098_);
v_str_1099_ = lean_ctor_get(v_x_1089_, 1);
lean_inc_ref(v_str_1099_);
lean_dec_ref_known(v_x_1089_, 2);
v_pre_1100_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_pre_1100_);
v_str_1101_ = lean_ctor_get(v_x_1090_, 1);
lean_inc_ref(v_str_1101_);
lean_dec_ref_known(v_x_1090_, 2);
v___x_1102_ = lean_apply_4(v_h__2_1092_, v_pre_1098_, v_str_1099_, v_pre_1100_, v_str_1101_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; 
lean_dec(v_h__2_1092_);
v___x_1103_ = lean_apply_5(v_h__4_1094_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1103_;
}
}
default: 
{
lean_dec(v_h__2_1092_);
lean_dec(v_h__1_1091_);
if (lean_obj_tag(v_x_1090_) == 2)
{
lean_object* v_pre_1104_; lean_object* v_i_1105_; lean_object* v_pre_1106_; lean_object* v_i_1107_; lean_object* v___x_1108_; 
lean_dec(v_h__4_1094_);
v_pre_1104_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_pre_1104_);
v_i_1105_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_i_1105_);
lean_dec_ref_known(v_x_1089_, 2);
v_pre_1106_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_pre_1106_);
v_i_1107_ = lean_ctor_get(v_x_1090_, 1);
lean_inc(v_i_1107_);
lean_dec_ref_known(v_x_1090_, 2);
v___x_1108_ = lean_apply_4(v_h__3_1093_, v_pre_1104_, v_i_1105_, v_pre_1106_, v_i_1107_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_h__3_1093_);
v___x_1109_ = lean_apply_5(v_h__4_1094_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1110_, lean_object* v_b_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_name_eq(v_a_1110_, v_b_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1113_, lean_object* v_b_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Lean_Name_instDecidableEq(v_a_1113_, v_b_1114_);
lean_dec(v_b_1114_);
lean_dec(v_a_1113_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1117_){
_start:
{
lean_object* v_namePrefix_1118_; lean_object* v_idx_1119_; lean_object* v___x_1120_; 
v_namePrefix_1118_ = lean_ctor_get(v_g_1117_, 0);
lean_inc(v_namePrefix_1118_);
v_idx_1119_ = lean_ctor_get(v_g_1117_, 1);
lean_inc(v_idx_1119_);
lean_dec_ref(v_g_1117_);
v___x_1120_ = l_Lean_Name_num___override(v_namePrefix_1118_, v_idx_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1121_){
_start:
{
lean_object* v_namePrefix_1122_; lean_object* v_idx_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v_namePrefix_1122_ = lean_ctor_get(v_g_1121_, 0);
v_idx_1123_ = lean_ctor_get(v_g_1121_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_g_1121_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1125_ = v_g_1121_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_idx_1123_);
lean_inc(v_namePrefix_1122_);
lean_dec(v_g_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_idx_1123_, v___x_1127_);
lean_dec(v_idx_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_namePrefix_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1133_){
_start:
{
lean_object* v_namePrefix_1134_; lean_object* v_idx_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1147_; 
v_namePrefix_1134_ = lean_ctor_get(v_g_1133_, 0);
v_idx_1135_ = lean_ctor_get(v_g_1133_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_g_1133_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1137_ = v_g_1133_;
v_isShared_1138_ = v_isSharedCheck_1147_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_idx_1135_);
lean_inc(v_namePrefix_1134_);
lean_dec(v_g_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1147_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
lean_inc(v_idx_1135_);
lean_inc(v_namePrefix_1134_);
v___x_1139_ = l_Lean_Name_num___override(v_namePrefix_1134_, v_idx_1135_);
v___x_1140_ = lean_unsigned_to_nat(1u);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1140_);
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_nat_add(v_idx_1135_, v___x_1140_);
lean_dec(v_idx_1135_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_namePrefix_1134_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1142_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1148_, lean_object* v_r_1149_, lean_object* v_____r_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_apply_2(v_toPure_1148_, lean_box(0), v_r_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1152_, lean_object* v_setNGen_1153_, lean_object* v_toBind_1154_, lean_object* v_ngen_1155_){
_start:
{
lean_object* v_namePrefix_1156_; lean_object* v_idx_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1170_; 
v_namePrefix_1156_ = lean_ctor_get(v_ngen_1155_, 0);
v_idx_1157_ = lean_ctor_get(v_ngen_1155_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_ngen_1155_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1159_ = v_ngen_1155_;
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_idx_1157_);
lean_inc(v_namePrefix_1156_);
lean_dec(v_ngen_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_r_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_inc(v_idx_1157_);
lean_inc(v_namePrefix_1156_);
v_r_1161_ = l_Lean_Name_num___override(v_namePrefix_1156_, v_idx_1157_);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1162_, 0, v_toPure_1152_);
lean_closure_set(v___f_1162_, 1, v_r_1161_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_idx_1157_, v___x_1163_);
lean_dec(v_idx_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1164_);
v___x_1166_ = v___x_1159_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_namePrefix_1156_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_apply_1(v_setNGen_1153_, v___x_1166_);
v___x_1168_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1167_, v___f_1162_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_){
_start:
{
lean_object* v_toApplicative_1173_; lean_object* v_toBind_1174_; lean_object* v_getNGen_1175_; lean_object* v_setNGen_1176_; lean_object* v_toPure_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v_toApplicative_1173_ = lean_ctor_get(v_inst_1171_, 0);
lean_inc_ref(v_toApplicative_1173_);
v_toBind_1174_ = lean_ctor_get(v_inst_1171_, 1);
lean_inc_n(v_toBind_1174_, 2);
lean_dec_ref(v_inst_1171_);
v_getNGen_1175_ = lean_ctor_get(v_inst_1172_, 0);
lean_inc(v_getNGen_1175_);
v_setNGen_1176_ = lean_ctor_get(v_inst_1172_, 1);
lean_inc(v_setNGen_1176_);
lean_dec_ref(v_inst_1172_);
v_toPure_1177_ = lean_ctor_get(v_toApplicative_1173_, 1);
lean_inc(v_toPure_1177_);
lean_dec_ref(v_toApplicative_1173_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1178_, 0, v_toPure_1177_);
lean_closure_set(v___f_1178_, 1, v_setNGen_1176_);
lean_closure_set(v___f_1178_, 2, v_toBind_1174_);
v___x_1179_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v_getNGen_1175_, v___f_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_mkFreshId___redArg(v_inst_1181_, v_inst_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1184_, lean_object* v_inst_1185_, lean_object* v_ngen_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_apply_1(v_setNGen_1184_, v_ngen_1186_);
v___x_1188_ = lean_apply_2(v_inst_1185_, lean_box(0), v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1189_, lean_object* v_inst_1190_){
_start:
{
lean_object* v_getNGen_1191_; lean_object* v_setNGen_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1201_; 
v_getNGen_1191_ = lean_ctor_get(v_inst_1190_, 0);
v_setNGen_1192_ = lean_ctor_get(v_inst_1190_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_inst_1190_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1194_ = v_inst_1190_;
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_setNGen_1192_);
lean_inc(v_getNGen_1191_);
lean_dec(v_inst_1190_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_inc(v_inst_1189_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1196_, 0, v_setNGen_1192_);
lean_closure_set(v___f_1196_, 1, v_inst_1189_);
v___x_1197_ = lean_apply_2(v_inst_1189_, lean_box(0), v_getNGen_1191_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___f_1196_);
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___f_1196_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1202_, lean_object* v_n_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1204_, v_inst_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 0)
{
lean_dec(v_x_1207_);
return v_x_1208_;
}
else
{
lean_object* v_head_1210_; lean_object* v_tail_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1222_; 
v_head_1210_ = lean_ctor_get(v_x_1209_, 0);
v_tail_1211_ = lean_ctor_get(v_x_1209_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1209_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1213_ = v_x_1209_;
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_tail_1211_);
lean_inc(v_head_1210_);
lean_dec(v_x_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
lean_inc(v_x_1207_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 5);
lean_ctor_set(v___x_1213_, 1, v_x_1207_);
lean_ctor_set(v___x_1213_, 0, v_x_1208_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_x_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_x_1207_);
v___x_1216_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = l_String_quote(v_head_1210_);
v___x_1218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1216_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v_x_1208_ = v___x_1219_;
v_x_1209_ = v_tail_1211_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_dec(v_x_1223_);
return v_x_1224_;
}
else
{
lean_object* v_head_1226_; lean_object* v_tail_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1238_; 
v_head_1226_ = lean_ctor_get(v_x_1225_, 0);
v_tail_1227_ = lean_ctor_get(v_x_1225_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1229_ = v_x_1225_;
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_tail_1227_);
lean_inc(v_head_1226_);
lean_dec(v_x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
lean_inc(v_x_1223_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 5);
lean_ctor_set(v___x_1229_, 1, v_x_1223_);
lean_ctor_set(v___x_1229_, 0, v_x_1224_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_x_1224_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_x_1223_);
v___x_1232_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = l_String_quote(v_head_1226_);
v___x_1234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1232_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1223_, v___x_1235_, v_tail_1227_);
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = l_String_quote(v___y_1239_);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_x_1243_);
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v_tail_1245_; 
v_tail_1245_ = lean_ctor_get(v_x_1242_, 1);
if (lean_obj_tag(v_tail_1245_) == 0)
{
lean_object* v_head_1246_; lean_object* v___x_1247_; 
lean_dec(v_x_1243_);
v_head_1246_ = lean_ctor_get(v_x_1242_, 0);
lean_inc(v_head_1246_);
lean_dec_ref_known(v_x_1242_, 2);
v___x_1247_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1246_);
return v___x_1247_;
}
else
{
lean_object* v_head_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_inc(v_tail_1245_);
v_head_1248_ = lean_ctor_get(v_x_1242_, 0);
lean_inc(v_head_1248_);
lean_dec_ref_known(v_x_1242_, 2);
v___x_1249_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1248_);
v___x_1250_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1243_, v___x_1249_, v_tail_1245_);
return v___x_1250_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1263_ = lean_string_length(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1265_ = lean_nat_to_int(v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1270_){
_start:
{
if (lean_obj_tag(v_a_1270_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1272_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1273_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1270_, v___x_1272_);
v___x_1274_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1275_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___x_1273_);
v___x_1277_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1274_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Std_Format_fill(v___x_1279_);
return v___x_1280_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_unsigned_to_nat(2u);
v___x_1288_ = lean_nat_to_int(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_to_int(v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1297_, lean_object* v_prec_1298_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v_ns_1299_; lean_object* v___y_1301_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_ns_1299_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_ns_1299_);
lean_dec_ref_known(v_x_1297_, 1);
v___x_1310_ = lean_unsigned_to_nat(1024u);
v___x_1311_ = lean_nat_dec_le(v___x_1310_, v_prec_1298_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1301_ = v___x_1312_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1301_ = v___x_1313_;
goto v___jp_1300_;
}
v___jp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1302_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1303_ = lean_unsigned_to_nat(1024u);
v___x_1304_ = l_Lean_Name_reprPrec(v_ns_1299_, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
lean_inc(v___y_1301_);
v___x_1306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___y_1301_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = 0;
v___x_1308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*1, v___x_1307_);
v___x_1309_ = l_Repr_addAppParen(v___x_1308_, v_prec_1298_);
return v___x_1309_;
}
}
else
{
lean_object* v_n_1314_; lean_object* v_fields_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1339_; 
v_n_1314_ = lean_ctor_get(v_x_1297_, 0);
v_fields_1315_ = lean_ctor_get(v_x_1297_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1317_ = v_x_1297_;
v_isShared_1318_ = v_isSharedCheck_1339_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_fields_1315_);
lean_inc(v_n_1314_);
lean_dec(v_x_1297_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1339_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___y_1320_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = lean_unsigned_to_nat(1024u);
v___x_1336_ = lean_nat_dec_le(v___x_1335_, v_prec_1298_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1320_ = v___x_1337_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1320_ = v___x_1338_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1321_ = lean_box(1);
v___x_1322_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1323_ = lean_unsigned_to_nat(1024u);
v___x_1324_ = l_Lean_Name_reprPrec(v_n_1314_, v___x_1323_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 5);
lean_ctor_set(v___x_1317_, 1, v___x_1324_);
lean_ctor_set(v___x_1317_, 0, v___x_1322_);
v___x_1326_ = v___x_1317_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v___x_1321_);
v___x_1328_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1315_);
v___x_1329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
lean_inc(v___y_1320_);
v___x_1330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___y_1320_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = 0;
v___x_1332_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*1, v___x_1331_);
v___x_1333_ = l_Repr_addAppParen(v___x_1332_, v_prec_1298_);
return v___x_1333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1340_, lean_object* v_prec_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1340_, v_prec_1341_);
lean_dec(v_prec_1341_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_nat_to_int(v_a_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1345_, lean_object* v_n_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1348_, lean_object* v_n_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1348_, v_n_1349_);
lean_dec(v_n_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_dec(v_x_1356_);
return v_x_1357_;
}
else
{
lean_object* v_head_1359_; lean_object* v_tail_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1371_; 
v_head_1359_ = lean_ctor_get(v_x_1358_, 0);
v_tail_1360_ = lean_ctor_get(v_x_1358_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1362_ = v_x_1358_;
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_tail_1360_);
lean_inc(v_head_1359_);
lean_dec(v_x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
lean_inc(v_x_1356_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 5);
lean_ctor_set(v___x_1362_, 1, v_x_1356_);
lean_ctor_set(v___x_1362_, 0, v_x_1357_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_x_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_x_1356_);
v___x_1365_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1359_, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1365_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v_x_1357_ = v___x_1368_;
v_x_1358_ = v_tail_1360_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
lean_dec(v_x_1372_);
return v_x_1373_;
}
else
{
lean_object* v_head_1375_; lean_object* v_tail_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1387_; 
v_head_1375_ = lean_ctor_get(v_x_1374_, 0);
v_tail_1376_ = lean_ctor_get(v_x_1374_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_x_1374_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1378_ = v_x_1374_;
v_isShared_1379_ = v_isSharedCheck_1387_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_tail_1376_);
lean_inc(v_head_1375_);
lean_dec(v_x_1374_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1387_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
lean_inc(v_x_1372_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 5);
lean_ctor_set(v___x_1378_, 1, v_x_1372_);
lean_ctor_set(v___x_1378_, 0, v_x_1373_);
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_x_1373_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_x_1372_);
v___x_1381_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1375_, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1381_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1372_, v___x_1384_, v_tail_1376_);
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_x_1389_);
v___x_1390_ = lean_box(0);
return v___x_1390_;
}
else
{
lean_object* v_tail_1391_; 
v_tail_1391_ = lean_ctor_get(v_x_1388_, 1);
if (lean_obj_tag(v_tail_1391_) == 0)
{
lean_object* v_head_1392_; lean_object* v___x_1393_; 
lean_dec(v_x_1389_);
v_head_1392_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_head_1392_);
lean_dec_ref_known(v_x_1388_, 2);
v___x_1393_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1392_);
return v___x_1393_;
}
else
{
lean_object* v_head_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_inc(v_tail_1391_);
v_head_1394_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_head_1394_);
lean_dec_ref_known(v_x_1388_, 2);
v___x_1395_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1394_);
v___x_1396_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1389_, v___x_1395_, v_tail_1391_);
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1397_){
_start:
{
if (lean_obj_tag(v_a_1397_) == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1399_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1400_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1397_, v___x_1399_);
v___x_1401_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1402_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v___x_1400_);
v___x_1404_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1401_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = 0;
v___x_1408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*1, v___x_1407_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 0)
{
lean_dec(v_x_1418_);
return v_x_1419_;
}
else
{
lean_object* v_head_1421_; lean_object* v_tail_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1433_; 
v_head_1421_ = lean_ctor_get(v_x_1420_, 0);
v_tail_1422_ = lean_ctor_get(v_x_1420_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1420_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1424_ = v_x_1420_;
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_tail_1422_);
lean_inc(v_head_1421_);
lean_dec(v_x_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
lean_inc(v_x_1418_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set_tag(v___x_1424_, 5);
lean_ctor_set(v___x_1424_, 1, v_x_1418_);
lean_ctor_set(v___x_1424_, 0, v_x_1419_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_x_1419_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_x_1418_);
v___x_1427_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = l_Lean_Syntax_instRepr_repr(v_head_1421_, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1427_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v_x_1419_ = v___x_1430_;
v_x_1420_ = v_tail_1422_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_dec(v_x_1434_);
return v_x_1435_;
}
else
{
lean_object* v_head_1437_; lean_object* v_tail_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1449_; 
v_head_1437_ = lean_ctor_get(v_x_1436_, 0);
v_tail_1438_ = lean_ctor_get(v_x_1436_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_x_1436_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1440_ = v_x_1436_;
v_isShared_1441_ = v_isSharedCheck_1449_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_tail_1438_);
lean_inc(v_head_1437_);
lean_dec(v_x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1449_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
lean_inc(v_x_1434_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 5);
lean_ctor_set(v___x_1440_, 1, v_x_1434_);
lean_ctor_set(v___x_1440_, 0, v_x_1435_);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_x_1435_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_x_1434_);
v___x_1443_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = l_Lean_Syntax_instRepr_repr(v_head_1437_, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1443_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1434_, v___x_1446_, v_tail_1438_);
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_x_1451_);
v___x_1452_ = lean_box(0);
return v___x_1452_;
}
else
{
lean_object* v_tail_1453_; 
v_tail_1453_ = lean_ctor_get(v_x_1450_, 1);
if (lean_obj_tag(v_tail_1453_) == 0)
{
lean_object* v_head_1454_; lean_object* v___x_1455_; 
lean_dec(v_x_1451_);
v_head_1454_ = lean_ctor_get(v_x_1450_, 0);
lean_inc(v_head_1454_);
lean_dec_ref_known(v_x_1450_, 2);
v___x_1455_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1454_);
return v___x_1455_;
}
else
{
lean_object* v_head_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_inc(v_tail_1453_);
v_head_1456_ = lean_ctor_get(v_x_1450_, 0);
lean_inc(v_head_1456_);
lean_dec_ref_known(v_x_1450_, 2);
v___x_1457_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1456_);
v___x_1458_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1451_, v___x_1457_, v_tail_1453_);
return v___x_1458_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1461_ = lean_string_length(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1463_ = lean_nat_to_int(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_array_get_size(v_xs_1469_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_nat_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1473_ = lean_array_to_list(v_xs_1469_);
v___x_1474_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1475_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1473_, v___x_1474_);
v___x_1476_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1477_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1475_);
v___x_1479_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1476_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Std_Format_fill(v___x_1481_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; 
lean_dec_ref(v_xs_1469_);
v___x_1483_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1497_, lean_object* v_prec_1498_){
_start:
{
lean_object* v___y_1500_; 
switch(lean_obj_tag(v_x_1497_))
{
case 0:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = lean_unsigned_to_nat(1024u);
v___x_1507_ = lean_nat_dec_le(v___x_1506_, v_prec_1498_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1500_ = v___x_1508_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1500_ = v___x_1509_;
goto v___jp_1499_;
}
}
case 1:
{
lean_object* v_info_1510_; lean_object* v_kind_1511_; lean_object* v_args_1512_; lean_object* v___y_1514_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_info_1510_ = lean_ctor_get(v_x_1497_, 0);
lean_inc(v_info_1510_);
v_kind_1511_ = lean_ctor_get(v_x_1497_, 1);
lean_inc(v_kind_1511_);
v_args_1512_ = lean_ctor_get(v_x_1497_, 2);
lean_inc_ref(v_args_1512_);
lean_dec_ref_known(v_x_1497_, 3);
v___x_1530_ = lean_unsigned_to_nat(1024u);
v___x_1531_ = lean_nat_dec_le(v___x_1530_, v_prec_1498_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1514_ = v___x_1532_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1514_ = v___x_1533_;
goto v___jp_1513_;
}
v___jp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1515_ = lean_box(1);
v___x_1516_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1517_ = lean_unsigned_to_nat(1024u);
v___x_1518_ = l_instReprSourceInfo_repr(v_info_1510_, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1516_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___x_1515_);
v___x_1521_ = l_Lean_Name_reprPrec(v_kind_1511_, v___x_1517_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1515_);
v___x_1524_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1512_);
v___x_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_inc(v___y_1514_);
v___x_1526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___y_1514_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = 0;
v___x_1528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*1, v___x_1527_);
v___x_1529_ = l_Repr_addAppParen(v___x_1528_, v_prec_1498_);
return v___x_1529_;
}
}
case 2:
{
lean_object* v_info_1534_; lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1560_; 
v_info_1534_ = lean_ctor_get(v_x_1497_, 0);
v_val_1535_ = lean_ctor_get(v_x_1497_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_x_1497_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1537_ = v_x_1497_;
v_isShared_1538_ = v_isSharedCheck_1560_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_inc(v_info_1534_);
lean_dec(v_x_1497_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1560_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___y_1540_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(1024u);
v___x_1557_ = lean_nat_dec_le(v___x_1556_, v_prec_1498_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1540_ = v___x_1558_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1540_ = v___x_1559_;
goto v___jp_1539_;
}
v___jp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1541_ = lean_box(1);
v___x_1542_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1543_ = lean_unsigned_to_nat(1024u);
v___x_1544_ = l_instReprSourceInfo_repr(v_info_1534_, v___x_1543_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 5);
lean_ctor_set(v___x_1537_, 1, v___x_1544_);
lean_ctor_set(v___x_1537_, 0, v___x_1542_);
v___x_1546_ = v___x_1537_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1541_);
v___x_1548_ = l_String_quote(v_val_1535_);
v___x_1549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
lean_inc(v___y_1540_);
v___x_1551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___y_1540_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = 0;
v___x_1553_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*1, v___x_1552_);
v___x_1554_ = l_Repr_addAppParen(v___x_1553_, v_prec_1498_);
return v___x_1554_;
}
}
}
}
default: 
{
lean_object* v_info_1561_; lean_object* v_rawVal_1562_; lean_object* v_val_1563_; lean_object* v_preresolved_1564_; lean_object* v___y_1566_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_info_1561_ = lean_ctor_get(v_x_1497_, 0);
lean_inc(v_info_1561_);
v_rawVal_1562_ = lean_ctor_get(v_x_1497_, 1);
lean_inc_ref(v_rawVal_1562_);
v_val_1563_ = lean_ctor_get(v_x_1497_, 2);
lean_inc(v_val_1563_);
v_preresolved_1564_ = lean_ctor_get(v_x_1497_, 3);
lean_inc(v_preresolved_1564_);
lean_dec_ref_known(v_x_1497_, 4);
v___x_1589_ = lean_unsigned_to_nat(1024u);
v___x_1590_ = lean_nat_dec_le(v___x_1589_, v_prec_1498_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1566_ = v___x_1591_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1566_ = v___x_1592_;
goto v___jp_1565_;
}
v___jp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1567_ = lean_box(1);
v___x_1568_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1569_ = lean_unsigned_to_nat(1024u);
v___x_1570_ = l_instReprSourceInfo_repr(v_info_1561_, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1568_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1567_);
v___x_1573_ = lean_substring_tostring(v_rawVal_1562_);
v___x_1574_ = l_String_quote(v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1576_ = lean_string_append(v___x_1574_, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1572_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___x_1567_);
v___x_1580_ = l_Lean_Name_reprPrec(v_val_1563_, v___x_1569_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___x_1567_);
v___x_1583_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1564_);
v___x_1584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
lean_inc(v___y_1566_);
v___x_1585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___y_1566_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = 0;
v___x_1587_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*1, v___x_1586_);
v___x_1588_ = l_Repr_addAppParen(v___x_1587_, v_prec_1498_);
return v___x_1588_;
}
}
}
v___jp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1500_);
v___x_1502_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = 0;
v___x_1504_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*1, v___x_1503_);
v___x_1505_ = l_Repr_addAppParen(v___x_1504_, v_prec_1498_);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = l_Lean_Syntax_instRepr_repr(v___y_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1596_, lean_object* v_prec_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Syntax_instRepr_repr(v_x_1596_, v_prec_1597_);
lean_dec(v_prec_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1599_, lean_object* v_n_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1602_, lean_object* v_n_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1602_, v_n_1603_);
lean_dec(v_n_1603_);
return v_res_1604_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(7u);
v___x_1621_ = lean_nat_to_int(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1624_ = lean_string_length(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1626_ = lean_nat_to_int(v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1632_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1633_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = l_Lean_Syntax_instRepr_repr(v_x_1631_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1633_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = 0;
v___x_1638_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*1, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1632_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1641_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___x_1639_);
v___x_1643_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1640_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*1, v___x_1637_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1647_, lean_object* v_x_1648_, lean_object* v_prec_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1651_, lean_object* v_x_1652_, lean_object* v_prec_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1651_, v_x_1652_, v_prec_1653_);
lean_dec(v_prec_1653_);
lean_dec(v_ks_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1656_, 0, v_ks_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1657_){
_start:
{
lean_inc(v_stx_1657_);
return v_stx_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1658_);
lean_dec(v_stx_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1662_; 
v___f_1662_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1665_, lean_object* v_ks_1666_){
_start:
{
lean_object* v___f_1667_; 
v___f_1667_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1668_, lean_object* v_ks_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1668_, v_ks_1669_);
lean_dec(v_ks_1669_);
lean_dec(v_k_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1672_; 
v___f_1672_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1675_, lean_object* v_k_x27_1676_){
_start:
{
lean_object* v___f_1677_; 
v___f_1677_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1678_, lean_object* v_k_x27_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1678_, v_k_x27_1679_);
lean_dec(v_k_x27_1679_);
lean_dec(v_ks_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1681_){
_start:
{
lean_inc(v_s_1681_);
return v_s_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1682_);
lean_dec(v_s_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1686_, lean_object* v_ss_1687_, lean_object* v_n_1688_, lean_object* v_res_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1690_, 0, v_info_1686_);
lean_ctor_set(v___x_1690_, 1, v_ss_1687_);
lean_ctor_set(v___x_1690_, 2, v_n_1688_);
lean_ctor_set(v___x_1690_, 3, v_res_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1700_; 
v___f_1700_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1703_){
_start:
{
lean_object* v___f_1704_; 
v___f_1704_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1705_);
lean_dec(v_k_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1708_, 0, v_k_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
if (lean_obj_tag(v_x_1710_) == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = 1;
return v___x_1711_;
}
else
{
uint8_t v___x_1712_; 
v___x_1712_ = 0;
return v___x_1712_;
}
}
else
{
if (lean_obj_tag(v_x_1710_) == 0)
{
uint8_t v___x_1713_; 
v___x_1713_ = 0;
return v___x_1713_;
}
else
{
lean_object* v_head_1714_; lean_object* v_tail_1715_; lean_object* v_head_1716_; lean_object* v_tail_1717_; uint8_t v___x_1718_; 
v_head_1714_ = lean_ctor_get(v_x_1709_, 0);
v_tail_1715_ = lean_ctor_get(v_x_1709_, 1);
v_head_1716_ = lean_ctor_get(v_x_1710_, 0);
v_tail_1717_ = lean_ctor_get(v_x_1710_, 1);
v___x_1718_ = lean_string_dec_eq(v_head_1714_, v_head_1716_);
if (v___x_1718_ == 0)
{
return v___x_1718_;
}
else
{
v_x_1709_ = v_tail_1715_;
v_x_1710_ = v_tail_1717_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1720_, v_x_1721_);
lean_dec(v_x_1721_);
lean_dec(v_x_1720_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
if (lean_obj_tag(v_x_1725_) == 0)
{
lean_object* v_ns_1726_; lean_object* v_ns_1727_; uint8_t v___x_1728_; 
v_ns_1726_ = lean_ctor_get(v_x_1724_, 0);
v_ns_1727_ = lean_ctor_get(v_x_1725_, 0);
v___x_1728_ = lean_name_eq(v_ns_1726_, v_ns_1727_);
return v___x_1728_;
}
else
{
uint8_t v___x_1729_; 
v___x_1729_ = 0;
return v___x_1729_;
}
}
else
{
if (lean_obj_tag(v_x_1725_) == 1)
{
lean_object* v_n_1730_; lean_object* v_fields_1731_; lean_object* v_n_1732_; lean_object* v_fields_1733_; uint8_t v___x_1734_; 
v_n_1730_ = lean_ctor_get(v_x_1724_, 0);
v_fields_1731_ = lean_ctor_get(v_x_1724_, 1);
v_n_1732_ = lean_ctor_get(v_x_1725_, 0);
v_fields_1733_ = lean_ctor_get(v_x_1725_, 1);
v___x_1734_ = lean_name_eq(v_n_1730_, v_n_1732_);
if (v___x_1734_ == 0)
{
return v___x_1734_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1731_, v_fields_1733_);
return v___x_1735_;
}
}
else
{
uint8_t v___x_1736_; 
v___x_1736_ = 0;
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_res_1739_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1737_, v_x_1738_);
lean_dec_ref(v_x_1738_);
lean_dec_ref(v_x_1737_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1743_) == 0)
{
if (lean_obj_tag(v_x_1744_) == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = 1;
return v___x_1745_;
}
else
{
uint8_t v___x_1746_; 
v___x_1746_ = 0;
return v___x_1746_;
}
}
else
{
if (lean_obj_tag(v_x_1744_) == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = 0;
return v___x_1747_;
}
else
{
lean_object* v_head_1748_; lean_object* v_tail_1749_; lean_object* v_head_1750_; lean_object* v_tail_1751_; uint8_t v___x_1752_; 
v_head_1748_ = lean_ctor_get(v_x_1743_, 0);
v_tail_1749_ = lean_ctor_get(v_x_1743_, 1);
v_head_1750_ = lean_ctor_get(v_x_1744_, 0);
v_tail_1751_ = lean_ctor_get(v_x_1744_, 1);
v___x_1752_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1748_, v_head_1750_);
if (v___x_1752_ == 0)
{
return v___x_1752_;
}
else
{
v_x_1743_ = v_tail_1749_;
v_x_1744_ = v_tail_1751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1754_, lean_object* v_x_1755_){
_start:
{
uint8_t v_res_1756_; lean_object* v_r_1757_; 
v_res_1756_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1754_, v_x_1755_);
lean_dec(v_x_1755_);
lean_dec(v_x_1754_);
v_r_1757_ = lean_box(v_res_1756_);
return v_r_1757_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
switch(lean_obj_tag(v_x_1758_))
{
case 0:
{
if (lean_obj_tag(v_x_1759_) == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = 1;
return v___x_1760_;
}
else
{
uint8_t v___x_1761_; 
v___x_1761_ = 0;
return v___x_1761_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1759_) == 1)
{
lean_object* v_kind_1762_; lean_object* v_args_1763_; lean_object* v_kind_1764_; lean_object* v_args_1765_; uint8_t v___x_1766_; 
v_kind_1762_ = lean_ctor_get(v_x_1758_, 1);
v_args_1763_ = lean_ctor_get(v_x_1758_, 2);
v_kind_1764_ = lean_ctor_get(v_x_1759_, 1);
v_args_1765_ = lean_ctor_get(v_x_1759_, 2);
v___x_1766_ = lean_name_eq(v_kind_1762_, v_kind_1764_);
if (v___x_1766_ == 0)
{
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = lean_array_get_size(v_args_1763_);
v___x_1768_ = lean_array_get_size(v_args_1765_);
v___x_1769_ = lean_nat_dec_eq(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
return v___x_1769_;
}
else
{
uint8_t v___x_1770_; 
v___x_1770_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1763_, v_args_1765_, v___x_1767_);
return v___x_1770_;
}
}
}
else
{
uint8_t v___x_1771_; 
v___x_1771_ = 0;
return v___x_1771_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1759_) == 2)
{
lean_object* v_val_1772_; lean_object* v_val_1773_; uint8_t v___x_1774_; 
v_val_1772_ = lean_ctor_get(v_x_1758_, 1);
v_val_1773_ = lean_ctor_get(v_x_1759_, 1);
v___x_1774_ = lean_string_dec_eq(v_val_1772_, v_val_1773_);
return v___x_1774_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = 0;
return v___x_1775_;
}
}
default: 
{
if (lean_obj_tag(v_x_1759_) == 3)
{
lean_object* v_rawVal_1776_; lean_object* v_val_1777_; lean_object* v_preresolved_1778_; lean_object* v_rawVal_1779_; lean_object* v_val_1780_; lean_object* v_preresolved_1781_; uint8_t v___y_1783_; uint8_t v___x_1785_; 
v_rawVal_1776_ = lean_ctor_get(v_x_1758_, 1);
v_val_1777_ = lean_ctor_get(v_x_1758_, 2);
v_preresolved_1778_ = lean_ctor_get(v_x_1758_, 3);
v_rawVal_1779_ = lean_ctor_get(v_x_1759_, 1);
v_val_1780_ = lean_ctor_get(v_x_1759_, 2);
v_preresolved_1781_ = lean_ctor_get(v_x_1759_, 3);
lean_inc_ref(v_rawVal_1779_);
lean_inc_ref(v_rawVal_1776_);
v___x_1785_ = lean_substring_beq(v_rawVal_1776_, v_rawVal_1779_);
if (v___x_1785_ == 0)
{
v___y_1783_ = v___x_1785_;
goto v___jp_1782_;
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_name_eq(v_val_1777_, v_val_1780_);
v___y_1783_ = v___x_1786_;
goto v___jp_1782_;
}
v___jp_1782_:
{
if (v___y_1783_ == 0)
{
return v___y_1783_;
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1778_, v_preresolved_1781_);
return v___x_1784_;
}
}
}
else
{
uint8_t v___x_1787_; 
v___x_1787_ = 0;
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1788_, lean_object* v_ys_1789_, lean_object* v_x_1790_){
_start:
{
lean_object* v_zero_1791_; uint8_t v_isZero_1792_; 
v_zero_1791_ = lean_unsigned_to_nat(0u);
v_isZero_1792_ = lean_nat_dec_eq(v_x_1790_, v_zero_1791_);
if (v_isZero_1792_ == 1)
{
lean_dec(v_x_1790_);
return v_isZero_1792_;
}
else
{
lean_object* v_one_1793_; lean_object* v_n_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_one_1793_ = lean_unsigned_to_nat(1u);
v_n_1794_ = lean_nat_sub(v_x_1790_, v_one_1793_);
lean_dec(v_x_1790_);
v___x_1795_ = lean_array_fget_borrowed(v_xs_1788_, v_n_1794_);
v___x_1796_ = lean_array_fget_borrowed(v_ys_1789_, v_n_1794_);
v___x_1797_ = l_Lean_Syntax_structEq(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec(v_n_1794_);
return v___x_1797_;
}
else
{
v_x_1790_ = v_n_1794_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1799_, lean_object* v_ys_1800_, lean_object* v_x_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1799_, v_ys_1800_, v_x_1801_);
lean_dec_ref(v_ys_1800_);
lean_dec_ref(v_xs_1799_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1804_, lean_object* v_x_1805_){
_start:
{
uint8_t v_res_1806_; lean_object* v_r_1807_; 
v_res_1806_ = l_Lean_Syntax_structEq(v_x_1804_, v_x_1805_);
lean_dec(v_x_1805_);
lean_dec(v_x_1804_);
v_r_1807_ = lean_box(v_res_1806_);
return v_r_1807_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1808_, lean_object* v_ys_1809_, lean_object* v_hsz_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1808_, v_ys_1809_, v_x_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1814_, lean_object* v_ys_1815_, lean_object* v_hsz_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
uint8_t v_res_1819_; lean_object* v_r_1820_; 
v_res_1819_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1814_, v_ys_1815_, v_hsz_1816_, v_x_1817_, v_x_1818_);
lean_dec_ref(v_ys_1815_);
lean_dec_ref(v_xs_1814_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1825_; 
v___f_1825_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1828_){
_start:
{
lean_object* v___f_1829_; 
v___f_1829_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Syntax_instBEqTSyntax(v_k_1830_);
lean_dec(v_k_1830_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1832_, lean_object* v_i_1833_){
_start:
{
lean_object* v_zero_1834_; uint8_t v_isZero_1835_; 
v_zero_1834_ = lean_unsigned_to_nat(0u);
v_isZero_1835_ = lean_nat_dec_eq(v_i_1833_, v_zero_1834_);
if (v_isZero_1835_ == 1)
{
lean_object* v___x_1836_; 
lean_dec(v_i_1833_);
v___x_1836_ = lean_box(0);
return v___x_1836_;
}
else
{
lean_object* v_one_1837_; lean_object* v_n_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_one_1837_ = lean_unsigned_to_nat(1u);
v_n_1838_ = lean_nat_sub(v_i_1833_, v_one_1837_);
lean_dec(v_i_1833_);
v___x_1839_ = lean_array_fget_borrowed(v_as_1832_, v_n_1838_);
v___x_1840_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
v_i_1833_ = v_n_1838_;
goto _start;
}
else
{
lean_dec(v_n_1838_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1842_){
_start:
{
switch(lean_obj_tag(v_x_1842_))
{
case 2:
{
lean_object* v_info_1843_; lean_object* v___x_1844_; 
v_info_1843_ = lean_ctor_get(v_x_1842_, 0);
lean_inc(v_info_1843_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_info_1843_);
return v___x_1844_;
}
case 3:
{
lean_object* v_info_1845_; lean_object* v___x_1846_; 
v_info_1845_ = lean_ctor_get(v_x_1842_, 0);
lean_inc(v_info_1845_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_info_1845_);
return v___x_1846_;
}
case 1:
{
lean_object* v_info_1847_; 
v_info_1847_ = lean_ctor_get(v_x_1842_, 0);
if (lean_obj_tag(v_info_1847_) == 2)
{
lean_object* v_args_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_args_1848_ = lean_ctor_get(v_x_1842_, 2);
v___x_1849_ = lean_array_get_size(v_args_1848_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1848_, v___x_1849_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; 
lean_inc(v_info_1847_);
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_info_1847_);
return v___x_1851_;
}
}
default: 
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_box(0);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1853_);
lean_dec(v_x_1853_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1855_, lean_object* v_i_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1855_, v_i_1856_);
lean_dec_ref(v_as_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1858_, lean_object* v_i_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1858_, v_i_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1862_, v_i_1863_, v_a_1864_);
lean_dec_ref(v_as_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_box(2);
return v___x_1868_;
}
else
{
lean_object* v_val_1869_; 
v_val_1869_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1867_, 1);
return v_val_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Syntax_getTailInfo(v_stx_1870_);
lean_dec(v_stx_1870_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1872_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v_val_1874_; 
v_val_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v___x_1873_, 1);
if (lean_obj_tag(v_val_1874_) == 0)
{
lean_object* v_trailing_1875_; lean_object* v_startPos_1876_; lean_object* v_stopPos_1877_; lean_object* v___x_1878_; 
v_trailing_1875_ = lean_ctor_get(v_val_1874_, 2);
lean_inc_ref(v_trailing_1875_);
lean_dec_ref_known(v_val_1874_, 4);
v_startPos_1876_ = lean_ctor_get(v_trailing_1875_, 1);
lean_inc(v_startPos_1876_);
v_stopPos_1877_ = lean_ctor_get(v_trailing_1875_, 2);
lean_inc(v_stopPos_1877_);
lean_dec_ref(v_trailing_1875_);
v___x_1878_ = lean_nat_sub(v_stopPos_1877_, v_startPos_1876_);
lean_dec(v_startPos_1876_);
lean_dec(v_stopPos_1877_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; 
lean_dec(v_val_1874_);
v___x_1879_ = lean_unsigned_to_nat(0u);
return v___x_1879_;
}
}
else
{
lean_object* v___x_1880_; 
lean_dec(v___x_1873_);
v___x_1880_ = lean_unsigned_to_nat(0u);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Syntax_getTrailingSize(v_stx_1881_);
lean_dec(v_stx_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1883_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = l_Lean_Syntax_getTailInfo(v_stx_1883_);
v___x_1885_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1884_);
lean_dec(v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1886_);
lean_dec(v_stx_1886_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1888_, uint8_t v_canonicalOnly_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = l_Lean_Syntax_getTailInfo(v_stx_1888_);
v___x_1891_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1890_, v_canonicalOnly_1889_);
lean_dec(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1892_, lean_object* v_canonicalOnly_1893_){
_start:
{
uint8_t v_canonicalOnly_boxed_1894_; lean_object* v_res_1895_; 
v_canonicalOnly_boxed_1894_ = lean_unbox(v_canonicalOnly_1893_);
v_res_1895_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1892_, v_canonicalOnly_boxed_1894_);
lean_dec(v_stx_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1896_, uint8_t v_withLeading_1897_, uint8_t v_withTrailing_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Syntax_getHeadInfo(v_stx_1896_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_leading_1900_; lean_object* v_pos_1901_; lean_object* v___x_1902_; 
v_leading_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc_ref(v_leading_1900_);
v_pos_1901_ = lean_ctor_get(v___x_1899_, 1);
lean_inc(v_pos_1901_);
lean_dec_ref_known(v___x_1899_, 4);
v___x_1902_ = l_Lean_Syntax_getTailInfo(v_stx_1896_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_trailing_1903_; lean_object* v_endPos_1904_; lean_object* v_str_1905_; lean_object* v_startPos_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1920_; 
v_trailing_1903_ = lean_ctor_get(v___x_1902_, 2);
lean_inc_ref(v_trailing_1903_);
v_endPos_1904_ = lean_ctor_get(v___x_1902_, 3);
lean_inc(v_endPos_1904_);
lean_dec_ref_known(v___x_1902_, 4);
v_str_1905_ = lean_ctor_get(v_leading_1900_, 0);
v_startPos_1906_ = lean_ctor_get(v_leading_1900_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_leading_1900_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_leading_1900_, 2);
lean_dec(v_unused_1921_);
v___x_1908_ = v_leading_1900_;
v_isShared_1909_ = v_isSharedCheck_1920_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_startPos_1906_);
lean_inc(v_str_1905_);
lean_dec(v_leading_1900_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1920_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1918_; 
if (v_withLeading_1897_ == 0)
{
lean_dec(v_startPos_1906_);
v___y_1918_ = v_pos_1901_;
goto v___jp_1917_;
}
else
{
lean_dec(v_pos_1901_);
v___y_1918_ = v_startPos_1906_;
goto v___jp_1917_;
}
v___jp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 2, v___y_1912_);
lean_ctor_set(v___x_1908_, 1, v___y_1911_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_str_1905_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___y_1911_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v___y_1912_);
v___x_1914_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
v___jp_1917_:
{
if (v_withTrailing_1898_ == 0)
{
lean_dec_ref(v_trailing_1903_);
v___y_1911_ = v___y_1918_;
v___y_1912_ = v_endPos_1904_;
goto v___jp_1910_;
}
else
{
lean_object* v_stopPos_1919_; 
lean_dec(v_endPos_1904_);
v_stopPos_1919_ = lean_ctor_get(v_trailing_1903_, 2);
lean_inc(v_stopPos_1919_);
lean_dec_ref(v_trailing_1903_);
v___y_1911_ = v___y_1918_;
v___y_1912_ = v_stopPos_1919_;
goto v___jp_1910_;
}
}
}
}
else
{
lean_object* v___x_1922_; 
lean_dec(v___x_1902_);
lean_dec(v_pos_1901_);
lean_dec_ref(v_leading_1900_);
v___x_1922_ = lean_box(0);
return v___x_1922_;
}
}
else
{
lean_object* v___x_1923_; 
lean_dec(v___x_1899_);
v___x_1923_ = lean_box(0);
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1924_, lean_object* v_withLeading_1925_, lean_object* v_withTrailing_1926_){
_start:
{
uint8_t v_withLeading_boxed_1927_; uint8_t v_withTrailing_boxed_1928_; lean_object* v_res_1929_; 
v_withLeading_boxed_1927_ = lean_unbox(v_withLeading_1925_);
v_withTrailing_boxed_1928_ = lean_unbox(v_withTrailing_1926_);
v_res_1929_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1924_, v_withLeading_boxed_1927_, v_withTrailing_boxed_1928_);
lean_dec(v_stx_1924_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1930_, lean_object* v_f_1931_, lean_object* v_i_1932_){
_start:
{
lean_object* v_zero_1933_; uint8_t v_isZero_1934_; 
v_zero_1933_ = lean_unsigned_to_nat(0u);
v_isZero_1934_ = lean_nat_dec_eq(v_i_1932_, v_zero_1933_);
if (v_isZero_1934_ == 1)
{
lean_object* v___x_1935_; 
lean_dec(v_i_1932_);
lean_dec_ref(v_f_1931_);
lean_dec_ref(v_a_1930_);
v___x_1935_ = lean_box(0);
return v___x_1935_;
}
else
{
lean_object* v_one_1936_; lean_object* v_n_1937_; lean_object* v_v_1938_; lean_object* v___x_1939_; 
v_one_1936_ = lean_unsigned_to_nat(1u);
v_n_1937_ = lean_nat_sub(v_i_1932_, v_one_1936_);
lean_dec(v_i_1932_);
v_v_1938_ = lean_array_fget_borrowed(v_a_1930_, v_n_1937_);
lean_inc_ref(v_f_1931_);
lean_inc(v_v_1938_);
v___x_1939_ = lean_apply_1(v_f_1931_, v_v_1938_);
if (lean_obj_tag(v___x_1939_) == 0)
{
v_i_1932_ = v_n_1937_;
goto _start;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_f_1931_);
v_val_1941_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1943_ = v___x_1939_;
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_val_1941_);
lean_dec(v___x_1939_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_array_fset(v_a_1930_, v_n_1937_, v_val_1941_);
lean_dec(v_n_1937_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1950_, lean_object* v_a_1951_, lean_object* v_f_1952_, lean_object* v_i_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1951_, v_f_1952_, v_i_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1955_, lean_object* v_x_1956_){
_start:
{
switch(lean_obj_tag(v_x_1956_))
{
case 2:
{
lean_object* v_val_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_val_1957_ = lean_ctor_get(v_x_1956_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v_x_1956_, 0);
lean_dec(v_unused_1966_);
v___x_1959_ = v_x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_val_1957_);
lean_dec(v_x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_info_1955_);
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_info_1955_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_val_1957_);
v___x_1962_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
case 3:
{
lean_object* v_rawVal_1967_; lean_object* v_val_1968_; lean_object* v_preresolved_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_rawVal_1967_ = lean_ctor_get(v_x_1956_, 1);
v_val_1968_ = lean_ctor_get(v_x_1956_, 2);
v_preresolved_1969_ = lean_ctor_get(v_x_1956_, 3);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_x_1956_, 0);
lean_dec(v_unused_1978_);
v___x_1971_ = v_x_1956_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_preresolved_1969_);
lean_inc(v_val_1968_);
lean_inc(v_rawVal_1967_);
lean_dec(v_x_1956_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_info_1955_);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_info_1955_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_rawVal_1967_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_val_1968_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_preresolved_1969_);
v___x_1974_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
}
case 1:
{
lean_object* v_info_1979_; lean_object* v_kind_1980_; lean_object* v_args_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1999_; 
v_info_1979_ = lean_ctor_get(v_x_1956_, 0);
v_kind_1980_ = lean_ctor_get(v_x_1956_, 1);
v_args_1981_ = lean_ctor_get(v_x_1956_, 2);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1983_ = v_x_1956_;
v_isShared_1984_ = v_isSharedCheck_1999_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_args_1981_);
lean_inc(v_kind_1980_);
lean_inc(v_info_1979_);
lean_dec(v_x_1956_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1999_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_array_get_size(v_args_1981_);
v___x_1986_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1955_, v_args_1981_, v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; 
lean_del_object(v___x_1983_);
lean_dec(v_kind_1980_);
lean_dec(v_info_1979_);
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1998_; 
v_val_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1998_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1998_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 2, v_val_1988_);
v___x_1993_ = v___x_1983_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_info_1979_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_kind_1980_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_val_1988_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2000_; 
lean_dec(v_x_1956_);
lean_dec(v_info_1955_);
v___x_2000_ = lean_box(0);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2001_, lean_object* v_a_2002_, lean_object* v_i_2003_){
_start:
{
lean_object* v_zero_2004_; uint8_t v_isZero_2005_; 
v_zero_2004_ = lean_unsigned_to_nat(0u);
v_isZero_2005_ = lean_nat_dec_eq(v_i_2003_, v_zero_2004_);
if (v_isZero_2005_ == 1)
{
lean_object* v___x_2006_; 
lean_dec(v_i_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_info_2001_);
v___x_2006_ = lean_box(0);
return v___x_2006_;
}
else
{
lean_object* v_one_2007_; lean_object* v_n_2008_; lean_object* v_v_2009_; lean_object* v___x_2010_; 
v_one_2007_ = lean_unsigned_to_nat(1u);
v_n_2008_ = lean_nat_sub(v_i_2003_, v_one_2007_);
lean_dec(v_i_2003_);
v_v_2009_ = lean_array_fget_borrowed(v_a_2002_, v_n_2008_);
lean_inc(v_v_2009_);
lean_inc(v_info_2001_);
v___x_2010_ = l_Lean_Syntax_setTailInfoAux(v_info_2001_, v_v_2009_);
if (lean_obj_tag(v___x_2010_) == 0)
{
v_i_2003_ = v_n_2008_;
goto _start;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_info_2001_);
v_val_2012_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_array_fset(v_a_2002_, v_n_2008_, v_val_2012_);
lean_dec(v_n_2008_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2021_, lean_object* v_info_2022_){
_start:
{
lean_object* v___x_2023_; 
lean_inc(v_stx_2021_);
v___x_2023_ = l_Lean_Syntax_setTailInfoAux(v_info_2022_, v_stx_2021_);
if (lean_obj_tag(v___x_2023_) == 0)
{
return v_stx_2021_;
}
else
{
lean_object* v_val_2024_; 
lean_dec(v_stx_2021_);
v_val_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v___x_2023_, 1);
return v_val_2024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Syntax_getTailInfo(v_stx_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_trailing_2027_; lean_object* v_leading_2028_; lean_object* v_pos_2029_; lean_object* v_endPos_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2048_; 
v_trailing_2027_ = lean_ctor_get(v___x_2026_, 2);
v_leading_2028_ = lean_ctor_get(v___x_2026_, 0);
v_pos_2029_ = lean_ctor_get(v___x_2026_, 1);
v_endPos_2030_ = lean_ctor_get(v___x_2026_, 3);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2032_ = v___x_2026_;
v_isShared_2033_ = v_isSharedCheck_2048_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_endPos_2030_);
lean_inc(v_trailing_2027_);
lean_inc(v_pos_2029_);
lean_inc(v_leading_2028_);
lean_dec(v___x_2026_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2048_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_str_2034_; lean_object* v_startPos_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2046_; 
v_str_2034_ = lean_ctor_get(v_trailing_2027_, 0);
v_startPos_2035_ = lean_ctor_get(v_trailing_2027_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_trailing_2027_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_trailing_2027_, 2);
lean_dec(v_unused_2047_);
v___x_2037_ = v_trailing_2027_;
v_isShared_2038_ = v_isSharedCheck_2046_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_startPos_2035_);
lean_inc(v_str_2034_);
lean_dec(v_trailing_2027_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2046_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
lean_inc(v_startPos_2035_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 2, v_startPos_2035_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_str_2034_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_startPos_2035_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_startPos_2035_);
v___x_2040_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 2, v___x_2040_);
v___x_2042_ = v___x_2032_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_leading_2028_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_pos_2029_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_endPos_2030_);
v___x_2042_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Syntax_setTailInfo(v_stx_2025_, v___x_2042_);
return v___x_2043_;
}
}
}
}
}
else
{
lean_dec(v___x_2026_);
return v_stx_2025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2049_, lean_object* v_f_2050_, lean_object* v_i_2051_){
_start:
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_array_get_size(v_a_2049_);
v___x_2053_ = lean_nat_dec_lt(v_i_2051_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
lean_dec(v_i_2051_);
lean_dec_ref(v_f_2050_);
lean_dec_ref(v_a_2049_);
v___x_2054_ = lean_box(0);
return v___x_2054_;
}
else
{
lean_object* v_v_2055_; lean_object* v___x_2056_; 
v_v_2055_ = lean_array_fget_borrowed(v_a_2049_, v_i_2051_);
lean_inc_ref(v_f_2050_);
lean_inc(v_v_2055_);
v___x_2056_ = lean_apply_1(v_f_2050_, v_v_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_nat_add(v_i_2051_, v___x_2057_);
lean_dec(v_i_2051_);
v_i_2051_ = v___x_2058_;
goto _start;
}
else
{
lean_object* v_val_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_f_2050_);
v_val_2060_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2056_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_val_2060_);
lean_dec(v___x_2056_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_array_fset(v_a_2049_, v_i_2051_, v_val_2060_);
lean_dec(v_i_2051_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2069_, lean_object* v_inst_2070_, lean_object* v_a_2071_, lean_object* v_f_2072_, lean_object* v_i_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2071_, v_f_2072_, v_i_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2075_, lean_object* v_inst_2076_, lean_object* v_a_2077_, lean_object* v_f_2078_, lean_object* v_i_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2075_, v_inst_2076_, v_a_2077_, v_f_2078_, v_i_2079_);
lean_dec(v_inst_2076_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2081_, lean_object* v_x_2082_){
_start:
{
switch(lean_obj_tag(v_x_2082_))
{
case 2:
{
lean_object* v_val_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_val_2083_ = lean_ctor_get(v_x_2082_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_x_2082_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v_x_2082_, 0);
lean_dec(v_unused_2092_);
v___x_2085_ = v_x_2082_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_val_2083_);
lean_dec(v_x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_info_2081_);
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_info_2081_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_val_2083_);
v___x_2088_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
}
case 3:
{
lean_object* v_rawVal_2093_; lean_object* v_val_2094_; lean_object* v_preresolved_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_rawVal_2093_ = lean_ctor_get(v_x_2082_, 1);
v_val_2094_ = lean_ctor_get(v_x_2082_, 2);
v_preresolved_2095_ = lean_ctor_get(v_x_2082_, 3);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2082_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_x_2082_, 0);
lean_dec(v_unused_2104_);
v___x_2097_ = v_x_2082_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_preresolved_2095_);
lean_inc(v_val_2094_);
lean_inc(v_rawVal_2093_);
lean_dec(v_x_2082_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v_info_2081_);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_info_2081_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_rawVal_2093_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_val_2094_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_preresolved_2095_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
}
case 1:
{
lean_object* v_info_2105_; lean_object* v_kind_2106_; lean_object* v_args_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2125_; 
v_info_2105_ = lean_ctor_get(v_x_2082_, 0);
v_kind_2106_ = lean_ctor_get(v_x_2082_, 1);
v_args_2107_ = lean_ctor_get(v_x_2082_, 2);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_x_2082_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2109_ = v_x_2082_;
v_isShared_2110_ = v_isSharedCheck_2125_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_args_2107_);
lean_inc(v_kind_2106_);
lean_inc(v_info_2105_);
lean_dec(v_x_2082_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2125_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2081_, v_args_2107_, v___x_2111_);
if (lean_obj_tag(v___x_2112_) == 1)
{
lean_object* v_val_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2123_; 
v_val_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2123_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_val_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2123_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 2, v_val_2113_);
v___x_2118_ = v___x_2109_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_info_2105_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_kind_2106_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_val_2113_);
v___x_2118_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2118_);
v___x_2120_ = v___x_2115_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2124_; 
lean_dec(v___x_2112_);
lean_del_object(v___x_2109_);
lean_dec(v_kind_2106_);
lean_dec(v_info_2105_);
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
}
}
default: 
{
lean_object* v___x_2126_; 
lean_dec(v_x_2082_);
lean_dec(v_info_2081_);
v___x_2126_ = lean_box(0);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2127_, lean_object* v_a_2128_, lean_object* v_i_2129_){
_start:
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = lean_array_get_size(v_a_2128_);
v___x_2131_ = lean_nat_dec_lt(v_i_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
lean_dec(v_i_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_info_2127_);
v___x_2132_ = lean_box(0);
return v___x_2132_;
}
else
{
lean_object* v_v_2133_; lean_object* v___x_2134_; 
v_v_2133_ = lean_array_fget_borrowed(v_a_2128_, v_i_2129_);
lean_inc(v_v_2133_);
lean_inc(v_info_2127_);
v___x_2134_ = l_Lean_Syntax_setHeadInfoAux(v_info_2127_, v_v_2133_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_add(v_i_2129_, v___x_2135_);
lean_dec(v_i_2129_);
v_i_2129_ = v___x_2136_;
goto _start;
}
else
{
lean_object* v_val_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_info_2127_);
v_val_2138_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v___x_2134_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_val_2138_);
lean_dec(v___x_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_array_fset(v_a_2128_, v_i_2129_, v_val_2138_);
lean_dec(v_i_2129_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2147_, lean_object* v_info_2148_){
_start:
{
lean_object* v___x_2149_; 
lean_inc(v_stx_2147_);
v___x_2149_ = l_Lean_Syntax_setHeadInfoAux(v_info_2148_, v_stx_2147_);
if (lean_obj_tag(v___x_2149_) == 0)
{
return v_stx_2147_;
}
else
{
lean_object* v_val_2150_; 
lean_dec(v_stx_2147_);
v_val_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2149_, 1);
return v_val_2150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2151_, lean_object* v_x_2152_){
_start:
{
switch(lean_obj_tag(v_x_2152_))
{
case 0:
{
lean_dec(v_info_2151_);
return v_x_2152_;
}
case 1:
{
lean_object* v_kind_2153_; lean_object* v_args_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_kind_2153_ = lean_ctor_get(v_x_2152_, 1);
v_args_2154_ = lean_ctor_get(v_x_2152_, 2);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_x_2152_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_x_2152_, 0);
lean_dec(v_unused_2162_);
v___x_2156_ = v_x_2152_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_args_2154_);
lean_inc(v_kind_2153_);
lean_dec(v_x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_info_2151_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_info_2151_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_kind_2153_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_args_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
case 2:
{
lean_object* v_val_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v_val_2163_ = lean_ctor_get(v_x_2152_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_x_2152_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v_x_2152_, 0);
lean_dec(v_unused_2171_);
v___x_2165_ = v_x_2152_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_val_2163_);
lean_dec(v_x_2152_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v_info_2151_);
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_info_2151_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_val_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
default: 
{
lean_object* v_rawVal_2172_; lean_object* v_val_2173_; lean_object* v_preresolved_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_rawVal_2172_ = lean_ctor_get(v_x_2152_, 1);
v_val_2173_ = lean_ctor_get(v_x_2152_, 2);
v_preresolved_2174_ = lean_ctor_get(v_x_2152_, 3);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_x_2152_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_x_2152_, 0);
lean_dec(v_unused_2182_);
v___x_2176_ = v_x_2152_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_preresolved_2174_);
lean_inc(v_val_2173_);
lean_inc(v_rawVal_2172_);
lean_dec(v_x_2152_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v_info_2151_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_info_2151_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_rawVal_2172_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_val_2173_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_preresolved_2174_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2186_){
_start:
{
switch(lean_obj_tag(v_x_2186_))
{
case 2:
{
lean_object* v_info_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; 
v_info_2187_ = lean_ctor_get(v_x_2186_, 0);
v___x_2188_ = 0;
v___x_2189_ = l_Lean_SourceInfo_getPos_x3f(v_info_2187_, v___x_2188_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; 
lean_dec_ref_known(v_x_2186_, 2);
v___x_2190_ = lean_box(0);
return v___x_2190_;
}
else
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v___x_2189_, 0);
lean_dec(v_unused_2198_);
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_x_2186_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_x_2186_);
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
case 3:
{
lean_object* v_info_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; 
v_info_2199_ = lean_ctor_get(v_x_2186_, 0);
v___x_2200_ = 0;
v___x_2201_ = l_Lean_SourceInfo_getPos_x3f(v_info_2199_, v___x_2200_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v___x_2202_; 
lean_dec_ref_known(v_x_2186_, 4);
v___x_2202_ = lean_box(0);
return v___x_2202_;
}
else
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2201_, 0);
lean_dec(v_unused_2210_);
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v_x_2186_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_x_2186_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
case 1:
{
lean_object* v_info_2211_; 
v_info_2211_ = lean_ctor_get(v_x_2186_, 0);
if (lean_obj_tag(v_info_2211_) == 2)
{
lean_object* v_args_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v_fst_2218_; 
v_args_2212_ = lean_ctor_get(v_x_2186_, 2);
lean_inc_ref(v_args_2212_);
lean_dec_ref_known(v_x_2186_, 3);
v___x_2213_ = lean_box(0);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2215_ = lean_array_size(v_args_2212_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2212_, v_sz_2215_, v___x_2216_, v___x_2214_);
lean_dec_ref(v_args_2212_);
v_fst_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_fst_2218_);
lean_dec_ref(v___x_2217_);
if (lean_obj_tag(v_fst_2218_) == 0)
{
return v___x_2213_;
}
else
{
lean_object* v_val_2219_; 
v_val_2219_ = lean_ctor_get(v_fst_2218_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v_fst_2218_, 1);
return v_val_2219_;
}
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v_x_2186_);
return v___x_2220_;
}
}
default: 
{
lean_object* v___x_2221_; 
lean_dec(v_x_2186_);
v___x_2221_ = lean_box(0);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_b_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
if (v___x_2226_ == 0)
{
lean_inc_ref(v_b_2225_);
return v_b_2225_;
}
else
{
lean_object* v___x_2227_; lean_object* v_a_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_box(0);
v_a_2228_ = lean_array_uget_borrowed(v_as_2222_, v_i_2224_);
lean_inc(v_a_2228_);
v___x_2229_ = l_Lean_Syntax_getHead_x3f(v_a_2228_);
if (lean_obj_tag(v___x_2229_) == 1)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___x_2227_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; 
lean_dec(v___x_2229_);
v___x_2232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2233_ = ((size_t)1ULL);
v___x_2234_ = lean_usize_add(v_i_2224_, v___x_2233_);
v_i_2224_ = v___x_2234_;
v_b_2225_ = v___x_2232_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2236_, lean_object* v_sz_2237_, lean_object* v_i_2238_, lean_object* v_b_2239_){
_start:
{
size_t v_sz_boxed_2240_; size_t v_i_boxed_2241_; lean_object* v_res_2242_; 
v_sz_boxed_2240_ = lean_unbox_usize(v_sz_2237_);
lean_dec(v_sz_2237_);
v_i_boxed_2241_ = lean_unbox_usize(v_i_2238_);
lean_dec(v_i_2238_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2236_, v_sz_boxed_2240_, v_i_boxed_2241_, v_b_2239_);
lean_dec_ref(v_b_2239_);
lean_dec_ref(v_as_2236_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2243_, lean_object* v_source_2244_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2245_ = l_Lean_Syntax_getHeadInfo(v_source_2244_);
v___x_2246_ = l_Lean_Syntax_setHeadInfo(v_target_2243_, v___x_2245_);
v___x_2247_ = l_Lean_Syntax_getTailInfo(v_source_2244_);
v___x_2248_ = l_Lean_Syntax_setTailInfo(v___x_2246_, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2249_, lean_object* v_source_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2249_, v_source_2250_);
lean_dec(v_source_2250_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2252_){
_start:
{
uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = 0;
v___x_2254_ = l_Lean_SourceInfo_fromRef(v_stx_2252_, v___x_2253_);
v___x_2255_ = l_Lean_Syntax_setHeadInfo(v_stx_2252_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2256_, lean_object* v_withRef_2257_, lean_object* v_x_2258_, lean_object* v_oldRef_2259_){
_start:
{
lean_object* v_ref_2260_; lean_object* v___x_2261_; 
v_ref_2260_ = l_Lean_replaceRef(v_val_2256_, v_oldRef_2259_);
v___x_2261_ = lean_apply_3(v_withRef_2257_, lean_box(0), v_ref_2260_, v_x_2258_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2262_, lean_object* v_withRef_2263_, lean_object* v_x_2264_, lean_object* v_oldRef_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2262_, v_withRef_2263_, v_x_2264_, v_oldRef_2265_);
lean_dec(v_oldRef_2265_);
lean_dec(v_val_2262_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2267_, lean_object* v_withRef_2268_, lean_object* v_toBind_2269_, lean_object* v_getRef_2270_, lean_object* v_____do__lift_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2271_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec(v_getRef_2270_);
lean_dec(v_toBind_2269_);
lean_dec(v_withRef_2268_);
return v_x_2267_;
}
else
{
lean_object* v_val_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; 
v_val_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2274_, 0, v_val_2273_);
lean_closure_set(v___f_2274_, 1, v_withRef_2268_);
lean_closure_set(v___f_2274_, 2, v_x_2267_);
v___x_2275_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v_getRef_2270_, v___f_2274_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v_toBind_2279_; lean_object* v_getRef_2280_; lean_object* v_withRef_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; 
v_toBind_2279_ = lean_ctor_get(v_inst_2276_, 1);
lean_inc_n(v_toBind_2279_, 2);
lean_dec_ref(v_inst_2276_);
v_getRef_2280_ = lean_ctor_get(v_inst_2277_, 0);
lean_inc_n(v_getRef_2280_, 2);
v_withRef_2281_ = lean_ctor_get(v_inst_2277_, 1);
lean_inc(v_withRef_2281_);
lean_dec_ref(v_inst_2277_);
v___f_2282_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2282_, 0, v_x_2278_);
lean_closure_set(v___f_2282_, 1, v_withRef_2281_);
lean_closure_set(v___f_2282_, 2, v_toBind_2279_);
lean_closure_set(v___f_2282_, 3, v_getRef_2280_);
v___x_2283_ = lean_apply_4(v_toBind_2279_, lean_box(0), lean_box(0), v_getRef_2280_, v___f_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_00_u03b1_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v_toBind_2289_; lean_object* v_getRef_2290_; lean_object* v_withRef_2291_; lean_object* v___f_2292_; lean_object* v___x_2293_; 
v_toBind_2289_ = lean_ctor_get(v_inst_2285_, 1);
lean_inc_n(v_toBind_2289_, 2);
lean_dec_ref(v_inst_2285_);
v_getRef_2290_ = lean_ctor_get(v_inst_2286_, 0);
lean_inc_n(v_getRef_2290_, 2);
v_withRef_2291_ = lean_ctor_get(v_inst_2286_, 1);
lean_inc(v_withRef_2291_);
lean_dec_ref(v_inst_2286_);
v___f_2292_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2292_, 0, v_x_2288_);
lean_closure_set(v___f_2292_, 1, v_withRef_2291_);
lean_closure_set(v___f_2292_, 2, v_toBind_2289_);
lean_closure_set(v___f_2292_, 3, v_getRef_2290_);
v___x_2293_ = lean_apply_4(v_toBind_2289_, lean_box(0), lean_box(0), v_getRef_2290_, v___f_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2303_, lean_object* v_k_2304_){
_start:
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2306_ = lean_name_eq(v_k_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
return v___x_2303_;
}
else
{
uint8_t v___x_2307_; 
v___x_2307_ = 0;
return v___x_2307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2308_, lean_object* v_k_2309_){
_start:
{
uint8_t v___x_1783__boxed_2310_; uint8_t v_res_2311_; lean_object* v_r_2312_; 
v___x_1783__boxed_2310_ = lean_unbox(v___x_2308_);
v_res_2311_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2310_, v_k_2309_);
lean_dec(v_k_2309_);
v_r_2312_ = lean_box(v_res_2311_);
return v_r_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2314_, lean_object* v_p_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
if (lean_obj_tag(v_stx_2314_) == 1)
{
lean_object* v_info_2318_; lean_object* v_kind_2319_; lean_object* v_args_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_info_2318_ = lean_ctor_get(v_stx_2314_, 0);
v_kind_2319_ = lean_ctor_get(v_stx_2314_, 1);
v_args_2320_ = lean_ctor_get(v_stx_2314_, 2);
lean_inc(v_kind_2319_);
v___x_2321_ = lean_apply_1(v_p_2315_, v_kind_2319_);
v___x_2322_ = lean_unbox(v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
lean_dec_ref(v_a_2316_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_stx_2314_);
lean_ctor_set(v___x_2323_, 1, v_a_2317_);
return v___x_2323_;
}
else
{
lean_object* v_methods_2324_; lean_object* v_quotContext_2325_; lean_object* v_currMacroScope_2326_; lean_object* v_currRecDepth_2327_; lean_object* v_maxRecDepth_2328_; lean_object* v_ref_2329_; lean_object* v_ref_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_methods_2324_ = lean_ctor_get(v_a_2316_, 0);
lean_inc_n(v_methods_2324_, 2);
v_quotContext_2325_ = lean_ctor_get(v_a_2316_, 1);
lean_inc_n(v_quotContext_2325_, 2);
v_currMacroScope_2326_ = lean_ctor_get(v_a_2316_, 2);
lean_inc_n(v_currMacroScope_2326_, 2);
v_currRecDepth_2327_ = lean_ctor_get(v_a_2316_, 3);
lean_inc_n(v_currRecDepth_2327_, 2);
v_maxRecDepth_2328_ = lean_ctor_get(v_a_2316_, 4);
lean_inc_n(v_maxRecDepth_2328_, 2);
v_ref_2329_ = lean_ctor_get(v_a_2316_, 5);
lean_inc(v_ref_2329_);
lean_dec_ref(v_a_2316_);
v_ref_2330_ = l_Lean_replaceRef(v_stx_2314_, v_ref_2329_);
lean_dec(v_ref_2329_);
lean_inc(v_ref_2330_);
v___x_2331_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2331_, 0, v_methods_2324_);
lean_ctor_set(v___x_2331_, 1, v_quotContext_2325_);
lean_ctor_set(v___x_2331_, 2, v_currMacroScope_2326_);
lean_ctor_set(v___x_2331_, 3, v_currRecDepth_2327_);
lean_ctor_set(v___x_2331_, 4, v_maxRecDepth_2328_);
lean_ctor_set(v___x_2331_, 5, v_ref_2330_);
lean_inc_ref(v_stx_2314_);
v___x_2332_ = l_Lean_Macro_expandMacro_x3f(v_stx_2314_, v___x_2331_, v_a_2317_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
if (lean_obj_tag(v_a_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2379_; 
lean_dec_ref_known(v___x_2331_, 6);
v_a_2334_ = lean_ctor_get(v___x_2332_, 1);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; 
v_unused_2380_ = lean_ctor_get(v___x_2332_, 0);
lean_dec(v_unused_2380_);
v___x_2336_ = v___x_2332_;
v_isShared_2337_ = v_isSharedCheck_2379_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2379_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_nat_dec_eq(v_currRecDepth_2327_, v_maxRecDepth_2328_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2370_; 
lean_inc_ref(v_args_2320_);
lean_inc(v_kind_2319_);
lean_inc(v_info_2318_);
lean_del_object(v___x_2336_);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_stx_2314_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; 
v_unused_2371_ = lean_ctor_get(v_stx_2314_, 2);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_stx_2314_, 1);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_stx_2314_, 0);
lean_dec(v_unused_2373_);
v___x_2340_ = v_stx_2314_;
v_isShared_2341_ = v_isSharedCheck_2370_;
goto v_resetjp_2339_;
}
else
{
lean_dec(v_stx_2314_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2370_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; size_t v_sz_2345_; size_t v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_add(v_currRecDepth_2327_, v___x_2342_);
lean_dec(v_currRecDepth_2327_);
v___x_2344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2344_, 0, v_methods_2324_);
lean_ctor_set(v___x_2344_, 1, v_quotContext_2325_);
lean_ctor_set(v___x_2344_, 2, v_currMacroScope_2326_);
lean_ctor_set(v___x_2344_, 3, v___x_2343_);
lean_ctor_set(v___x_2344_, 4, v_maxRecDepth_2328_);
lean_ctor_set(v___x_2344_, 5, v_ref_2330_);
v_sz_2345_ = lean_array_size(v_args_2320_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = lean_unbox(v___x_2321_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2347_, v_sz_2345_, v___x_2346_, v_args_2320_, v___x_2344_, v_a_2334_);
lean_dec_ref_known(v___x_2344_, 6);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2360_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_a_2350_ = lean_ctor_get(v___x_2348_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2352_ = v___x_2348_;
v_isShared_2353_ = v_isSharedCheck_2360_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2360_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 2, v_a_2349_);
v___x_2355_ = v___x_2340_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_info_2318_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_kind_2319_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_a_2349_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2355_);
v___x_2357_ = v___x_2352_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_a_2350_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_del_object(v___x_2340_);
lean_dec(v_kind_2319_);
lean_dec(v_info_2318_);
v_a_2361_ = lean_ctor_get(v___x_2348_, 0);
v_a_2362_ = lean_ctor_get(v___x_2348_, 1);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2348_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_inc(v_a_2361_);
lean_dec(v___x_2348_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2361_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
lean_dec(v_ref_2330_);
lean_dec(v_maxRecDepth_2328_);
lean_dec(v_currRecDepth_2327_);
lean_dec(v_currMacroScope_2326_);
lean_dec(v_quotContext_2325_);
lean_dec(v_methods_2324_);
v___x_2374_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v_stx_2314_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 1);
lean_ctor_set(v___x_2336_, 0, v___x_2375_);
v___x_2377_ = v___x_2336_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_a_2334_);
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
else
{
lean_object* v_a_2381_; lean_object* v_val_2382_; lean_object* v___f_2383_; 
lean_inc_ref(v_a_2333_);
lean_dec(v_ref_2330_);
lean_dec(v_maxRecDepth_2328_);
lean_dec(v_currRecDepth_2327_);
lean_dec(v_currMacroScope_2326_);
lean_dec(v_quotContext_2325_);
lean_dec(v_methods_2324_);
lean_dec_ref_known(v_stx_2314_, 3);
v_a_2381_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2332_, 2);
v_val_2382_ = lean_ctor_get(v_a_2333_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v_a_2333_, 1);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2383_, 0, v___x_2321_);
v_stx_2314_ = v_val_2382_;
v_p_2315_ = v___f_2383_;
v_a_2316_ = v___x_2331_;
v_a_2317_ = v_a_2381_;
goto _start;
}
}
else
{
lean_object* v_a_2385_; lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref_known(v___x_2331_, 6);
lean_dec(v_ref_2330_);
lean_dec(v_maxRecDepth_2328_);
lean_dec(v_currRecDepth_2327_);
lean_dec(v_currMacroScope_2326_);
lean_dec(v_quotContext_2325_);
lean_dec(v_methods_2324_);
lean_dec_ref_known(v_stx_2314_, 3);
v_a_2385_ = lean_ctor_get(v___x_2332_, 0);
v_a_2386_ = lean_ctor_get(v___x_2332_, 1);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2332_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_inc(v_a_2385_);
lean_dec(v___x_2332_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2385_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v___x_2394_; 
lean_dec_ref(v_a_2316_);
lean_dec_ref(v_p_2315_);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_stx_2314_);
lean_ctor_set(v___x_2394_, 1, v_a_2317_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2395_, size_t v_sz_2396_, size_t v_i_2397_, lean_object* v_bs_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = lean_usize_dec_lt(v_i_2397_, v_sz_2396_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_bs_2398_);
lean_ctor_set(v___x_2402_, 1, v___y_2400_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; lean_object* v___f_2404_; lean_object* v_v_2405_; lean_object* v___x_2406_; 
v___x_2403_ = lean_box(v___x_2395_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2404_, 0, v___x_2403_);
v_v_2405_ = lean_array_uget_borrowed(v_bs_2398_, v_i_2397_);
lean_inc_ref(v___y_2399_);
lean_inc(v_v_2405_);
v___x_2406_ = l_Lean_expandMacros(v_v_2405_, v___f_2404_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v_bs_x27_2410_; size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
v_a_2408_ = lean_ctor_get(v___x_2406_, 1);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2406_, 2);
v___x_2409_ = lean_unsigned_to_nat(0u);
v_bs_x27_2410_ = lean_array_uset(v_bs_2398_, v_i_2397_, v___x_2409_);
v___x_2411_ = ((size_t)1ULL);
v___x_2412_ = lean_usize_add(v_i_2397_, v___x_2411_);
v___x_2413_ = lean_array_uset(v_bs_x27_2410_, v_i_2397_, v_a_2407_);
v_i_2397_ = v___x_2412_;
v_bs_2398_ = v___x_2413_;
v___y_2400_ = v_a_2408_;
goto _start;
}
else
{
lean_object* v_a_2415_; lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v_bs_2398_);
v_a_2415_ = lean_ctor_get(v___x_2406_, 0);
v_a_2416_ = lean_ctor_get(v___x_2406_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2406_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_inc(v_a_2415_);
lean_dec(v___x_2406_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2424_, lean_object* v_sz_2425_, lean_object* v_i_2426_, lean_object* v_bs_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v___x_1802__boxed_2430_; size_t v_sz_boxed_2431_; size_t v_i_boxed_2432_; lean_object* v_res_2433_; 
v___x_1802__boxed_2430_ = lean_unbox(v___x_2424_);
v_sz_boxed_2431_ = lean_unbox_usize(v_sz_2425_);
lean_dec(v_sz_2425_);
v_i_boxed_2432_ = lean_unbox_usize(v_i_2426_);
lean_dec(v_i_2426_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1802__boxed_2430_, v_sz_boxed_2431_, v_i_boxed_2432_, v_bs_2427_, v___y_2428_, v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2434_, lean_object* v_val_2435_, uint8_t v_canonical_2436_){
_start:
{
lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2437_ = l_Lean_SourceInfo_fromRef(v_src_2434_, v_canonical_2436_);
v___x_2438_ = 1;
lean_inc(v_val_2435_);
v___x_2439_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2435_, v___x_2438_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = lean_string_utf8_byte_size(v___x_2439_);
v___x_2442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2439_);
lean_ctor_set(v___x_2442_, 1, v___x_2440_);
lean_ctor_set(v___x_2442_, 2, v___x_2441_);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2437_);
lean_ctor_set(v___x_2444_, 1, v___x_2442_);
lean_ctor_set(v___x_2444_, 2, v_val_2435_);
lean_ctor_set(v___x_2444_, 3, v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2445_, lean_object* v_val_2446_, lean_object* v_canonical_2447_){
_start:
{
uint8_t v_canonical_boxed_2448_; lean_object* v_res_2449_; 
v_canonical_boxed_2448_ = lean_unbox(v_canonical_2447_);
v_res_2449_ = l_Lean_mkIdentFrom(v_src_2445_, v_val_2446_, v_canonical_boxed_2448_);
lean_dec(v_src_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2465_, lean_object* v_text_2466_, uint8_t v_canonical_2467_){
_start:
{
lean_object* v_info_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_body_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_info_2468_ = l_Lean_SourceInfo_fromRef(v_src_2465_, v_canonical_2467_);
v___x_2469_ = lean_box(2);
v___x_2470_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2468_, 2);
v___x_2471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_info_2468_);
lean_ctor_set(v___x_2471_, 1, v_text_2466_);
v___x_2472_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_info_2468_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(2u);
v___x_2475_ = lean_mk_empty_array_with_capacity(v___x_2474_);
lean_inc_ref(v___x_2475_);
v___x_2476_ = lean_array_push(v___x_2475_, v___x_2471_);
v___x_2477_ = lean_array_push(v___x_2476_, v___x_2473_);
v_body_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2478_, 0, v___x_2469_);
lean_ctor_set(v_body_2478_, 1, v___x_2470_);
lean_ctor_set(v_body_2478_, 2, v___x_2477_);
v___x_2479_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2480_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_info_2468_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_array_push(v___x_2475_, v___x_2481_);
v___x_2483_ = lean_array_push(v___x_2482_, v_body_2478_);
v___x_2484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2469_);
lean_ctor_set(v___x_2484_, 1, v___x_2479_);
lean_ctor_set(v___x_2484_, 2, v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2485_, lean_object* v_text_2486_, lean_object* v_canonical_2487_){
_start:
{
uint8_t v_canonical_boxed_2488_; lean_object* v_res_2489_; 
v_canonical_boxed_2488_ = lean_unbox(v_canonical_2487_);
v_res_2489_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2485_, v_text_2486_, v_canonical_boxed_2488_);
lean_dec(v_src_2485_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2490_){
_start:
{
lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_box(0);
v___x_2492_ = 0;
v___x_2493_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2491_, v_text_2490_, v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2494_, uint8_t v_canonical_2495_, lean_object* v_toPure_2496_, lean_object* v_____do__lift_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = l_Lean_mkIdentFrom(v_____do__lift_2497_, v_val_2494_, v_canonical_2495_);
v___x_2499_ = lean_apply_2(v_toPure_2496_, lean_box(0), v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2500_, lean_object* v_canonical_2501_, lean_object* v_toPure_2502_, lean_object* v_____do__lift_2503_){
_start:
{
uint8_t v_canonical_boxed_2504_; lean_object* v_res_2505_; 
v_canonical_boxed_2504_ = lean_unbox(v_canonical_2501_);
v_res_2505_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2500_, v_canonical_boxed_2504_, v_toPure_2502_, v_____do__lift_2503_);
lean_dec(v_____do__lift_2503_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2506_, lean_object* v_inst_2507_, lean_object* v_val_2508_, uint8_t v_canonical_2509_){
_start:
{
lean_object* v_toApplicative_2510_; lean_object* v_toBind_2511_; lean_object* v_getRef_2512_; lean_object* v_toPure_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; lean_object* v___x_2516_; 
v_toApplicative_2510_ = lean_ctor_get(v_inst_2506_, 0);
lean_inc_ref(v_toApplicative_2510_);
v_toBind_2511_ = lean_ctor_get(v_inst_2506_, 1);
lean_inc(v_toBind_2511_);
lean_dec_ref(v_inst_2506_);
v_getRef_2512_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc(v_getRef_2512_);
lean_dec_ref(v_inst_2507_);
v_toPure_2513_ = lean_ctor_get(v_toApplicative_2510_, 1);
lean_inc(v_toPure_2513_);
lean_dec_ref(v_toApplicative_2510_);
v___x_2514_ = lean_box(v_canonical_2509_);
v___f_2515_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2515_, 0, v_val_2508_);
lean_closure_set(v___f_2515_, 1, v___x_2514_);
lean_closure_set(v___f_2515_, 2, v_toPure_2513_);
v___x_2516_ = lean_apply_4(v_toBind_2511_, lean_box(0), lean_box(0), v_getRef_2512_, v___f_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_val_2519_, lean_object* v_canonical_2520_){
_start:
{
uint8_t v_canonical_boxed_2521_; lean_object* v_res_2522_; 
v_canonical_boxed_2521_ = lean_unbox(v_canonical_2520_);
v_res_2522_ = l_Lean_mkIdentFromRef___redArg(v_inst_2517_, v_inst_2518_, v_val_2519_, v_canonical_boxed_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_val_2526_, uint8_t v_canonical_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_mkIdentFromRef___redArg(v_inst_2524_, v_inst_2525_, v_val_2526_, v_canonical_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_val_2532_, lean_object* v_canonical_2533_){
_start:
{
uint8_t v_canonical_boxed_2534_; lean_object* v_res_2535_; 
v_canonical_boxed_2534_ = lean_unbox(v_canonical_2533_);
v_res_2535_ = l_Lean_mkIdentFromRef(v_m_2529_, v_inst_2530_, v_inst_2531_, v_val_2532_, v_canonical_boxed_2534_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2539_, lean_object* v_c_2540_, uint8_t v_canonical_2541_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_id_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2542_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2543_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2540_);
v_id_2544_ = l_Lean_addMacroScope(v___x_2542_, v_c_2540_, v___x_2543_);
v___x_2545_ = l_Lean_SourceInfo_fromRef(v_src_2539_, v_canonical_2541_);
v___x_2546_ = 1;
lean_inc(v_id_2544_);
v___x_2547_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2544_, v___x_2546_);
v___x_2548_ = lean_string_utf8_byte_size(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2543_);
lean_ctor_set(v___x_2549_, 2, v___x_2548_);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_c_2540_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
lean_ctor_set(v___x_2552_, 1, v___x_2550_);
v___x_2553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2545_);
lean_ctor_set(v___x_2553_, 1, v___x_2549_);
lean_ctor_set(v___x_2553_, 2, v_id_2544_);
lean_ctor_set(v___x_2553_, 3, v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2554_, lean_object* v_c_2555_, lean_object* v_canonical_2556_){
_start:
{
uint8_t v_canonical_boxed_2557_; lean_object* v_res_2558_; 
v_canonical_boxed_2557_ = lean_unbox(v_canonical_2556_);
v_res_2558_ = l_Lean_mkCIdentFrom(v_src_2554_, v_c_2555_, v_canonical_boxed_2557_);
lean_dec(v_src_2554_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2559_, uint8_t v_canonical_2560_, lean_object* v_toPure_2561_, lean_object* v_____do__lift_2562_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = l_Lean_mkCIdentFrom(v_____do__lift_2562_, v_c_2559_, v_canonical_2560_);
v___x_2564_ = lean_apply_2(v_toPure_2561_, lean_box(0), v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2565_, lean_object* v_canonical_2566_, lean_object* v_toPure_2567_, lean_object* v_____do__lift_2568_){
_start:
{
uint8_t v_canonical_boxed_2569_; lean_object* v_res_2570_; 
v_canonical_boxed_2569_ = lean_unbox(v_canonical_2566_);
v_res_2570_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2565_, v_canonical_boxed_2569_, v_toPure_2567_, v_____do__lift_2568_);
lean_dec(v_____do__lift_2568_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_c_2573_, uint8_t v_canonical_2574_){
_start:
{
lean_object* v_toApplicative_2575_; lean_object* v_toBind_2576_; lean_object* v_getRef_2577_; lean_object* v_toPure_2578_; lean_object* v___x_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; 
v_toApplicative_2575_ = lean_ctor_get(v_inst_2571_, 0);
lean_inc_ref(v_toApplicative_2575_);
v_toBind_2576_ = lean_ctor_get(v_inst_2571_, 1);
lean_inc(v_toBind_2576_);
lean_dec_ref(v_inst_2571_);
v_getRef_2577_ = lean_ctor_get(v_inst_2572_, 0);
lean_inc(v_getRef_2577_);
lean_dec_ref(v_inst_2572_);
v_toPure_2578_ = lean_ctor_get(v_toApplicative_2575_, 1);
lean_inc(v_toPure_2578_);
lean_dec_ref(v_toApplicative_2575_);
v___x_2579_ = lean_box(v_canonical_2574_);
v___f_2580_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2580_, 0, v_c_2573_);
lean_closure_set(v___f_2580_, 1, v___x_2579_);
lean_closure_set(v___f_2580_, 2, v_toPure_2578_);
v___x_2581_ = lean_apply_4(v_toBind_2576_, lean_box(0), lean_box(0), v_getRef_2577_, v___f_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_c_2584_, lean_object* v_canonical_2585_){
_start:
{
uint8_t v_canonical_boxed_2586_; lean_object* v_res_2587_; 
v_canonical_boxed_2586_ = lean_unbox(v_canonical_2585_);
v_res_2587_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2582_, v_inst_2583_, v_c_2584_, v_canonical_boxed_2586_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_c_2591_, uint8_t v_canonical_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2589_, v_inst_2590_, v_c_2591_, v_canonical_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_c_2597_, lean_object* v_canonical_2598_){
_start:
{
uint8_t v_canonical_boxed_2599_; lean_object* v_res_2600_; 
v_canonical_boxed_2599_ = lean_unbox(v_canonical_2598_);
v_res_2600_ = l_Lean_mkCIdentFromRef(v_m_2594_, v_inst_2595_, v_inst_2596_, v_c_2597_, v_canonical_boxed_2599_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2601_){
_start:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = 0;
v___x_2604_ = l_Lean_mkCIdentFrom(v___x_2602_, v_c_2601_, v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2605_){
_start:
{
lean_object* v___x_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2606_ = lean_box(2);
v___x_2607_ = 1;
lean_inc(v_val_2605_);
v___x_2608_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2605_, v___x_2607_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_string_utf8_byte_size(v___x_2608_);
v___x_2611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2608_);
lean_ctor_set(v___x_2611_, 1, v___x_2609_);
lean_ctor_set(v___x_2611_, 2, v___x_2610_);
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2606_);
lean_ctor_set(v___x_2613_, 1, v___x_2611_);
lean_ctor_set(v___x_2613_, 2, v_val_2605_);
lean_ctor_set(v___x_2613_, 3, v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2619_ = lean_box(2);
v___x_2620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
lean_ctor_set(v___x_2620_, 2, v_args_2617_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2621_, lean_object* v_as_2622_, size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_b_2625_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_lt(v_i_2624_, v_sz_2623_);
if (v___x_2626_ == 0)
{
lean_dec(v_sep_2621_);
return v_b_2625_;
}
else
{
lean_object* v_fst_2627_; lean_object* v_snd_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2648_; 
v_fst_2627_ = lean_ctor_get(v_b_2625_, 0);
v_snd_2628_ = lean_ctor_get(v_b_2625_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_b_2625_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2630_ = v_b_2625_;
v_isShared_2631_ = v_isSharedCheck_2648_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snd_2628_);
lean_inc(v_fst_2627_);
lean_dec(v_b_2625_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2648_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_r_2633_; lean_object* v_i_2642_; lean_object* v_a_2643_; uint8_t v___x_2644_; 
v_i_2642_ = lean_unsigned_to_nat(0u);
v_a_2643_ = lean_array_uget_borrowed(v_as_2622_, v_i_2624_);
v___x_2644_ = lean_nat_dec_lt(v_i_2642_, v_fst_2627_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; 
lean_inc(v_a_2643_);
v___x_2645_ = lean_array_push(v_snd_2628_, v_a_2643_);
v_r_2633_ = v___x_2645_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_inc(v_sep_2621_);
v___x_2646_ = lean_array_push(v_snd_2628_, v_sep_2621_);
lean_inc(v_a_2643_);
v___x_2647_ = lean_array_push(v___x_2646_, v_a_2643_);
v_r_2633_ = v___x_2647_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_add(v_fst_2627_, v___x_2634_);
lean_dec(v_fst_2627_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v_r_2633_);
lean_ctor_set(v___x_2630_, 0, v___x_2635_);
v___x_2637_ = v___x_2630_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_r_2633_);
v___x_2637_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
size_t v___x_2638_; size_t v___x_2639_; 
v___x_2638_ = ((size_t)1ULL);
v___x_2639_ = lean_usize_add(v_i_2624_, v___x_2638_);
v_i_2624_ = v___x_2639_;
v_b_2625_ = v___x_2637_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2649_, lean_object* v_as_2650_, lean_object* v_sz_2651_, lean_object* v_i_2652_, lean_object* v_b_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2651_);
lean_dec(v_sz_2651_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2652_);
lean_dec(v_i_2652_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2649_, v_as_2650_, v_sz_boxed_2654_, v_i_boxed_2655_, v_b_2653_);
lean_dec_ref(v_as_2650_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2662_, lean_object* v_sep_2663_){
_start:
{
lean_object* v___x_2664_; size_t v_sz_2665_; size_t v___x_2666_; lean_object* v___x_2667_; lean_object* v_snd_2668_; 
v___x_2664_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2665_ = lean_array_size(v_as_2662_);
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2663_, v_as_2662_, v_sz_2665_, v___x_2666_, v___x_2664_);
v_snd_2668_ = lean_ctor_get(v___x_2667_, 1);
lean_inc(v_snd_2668_);
lean_dec_ref(v___x_2667_);
return v_snd_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2669_, lean_object* v_sep_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_mkSepArray(v_as_2669_, v_sep_2670_);
lean_dec_ref(v_as_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2679_){
_start:
{
if (lean_obj_tag(v_arg_2679_) == 0)
{
lean_object* v___x_2680_; 
v___x_2680_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2680_;
}
else
{
lean_object* v_val_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_val_2681_ = lean_ctor_get(v_arg_2679_, 0);
lean_inc(v_val_2681_);
lean_dec_ref_known(v_arg_2679_, 1);
v___x_2682_ = lean_unsigned_to_nat(1u);
v___x_2683_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2684_ = lean_array_push(v___x_2683_, v_val_2681_);
v___x_2685_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2686_ = lean_box(2);
v___x_2687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v___x_2685_);
lean_ctor_set(v___x_2687_, 2, v___x_2684_);
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2694_, uint8_t v_canonical_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2696_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2697_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2698_ = l_Lean_mkAtomFrom(v_ref_2694_, v___x_2697_, v_canonical_2695_);
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = lean_mk_empty_array_with_capacity(v___x_2699_);
v___x_2701_ = lean_array_push(v___x_2700_, v___x_2698_);
v___x_2702_ = lean_box(2);
v___x_2703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2696_);
lean_ctor_set(v___x_2703_, 2, v___x_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2704_, lean_object* v_canonical_2705_){
_start:
{
uint8_t v_canonical_boxed_2706_; lean_object* v_res_2707_; 
v_canonical_boxed_2706_ = lean_unbox(v_canonical_2705_);
v_res_2707_ = l_Lean_mkHole(v_ref_2704_, v_canonical_boxed_2706_);
lean_dec(v_ref_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2708_, lean_object* v_sep_2709_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2710_ = l_Lean_mkSepArray(v_a_2708_, v_sep_2709_);
v___x_2711_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2712_ = lean_box(2);
v___x_2713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2711_);
lean_ctor_set(v___x_2713_, 2, v___x_2710_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2714_, lean_object* v_sep_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Syntax_mkSep(v_a_2714_, v_sep_2715_);
lean_dec_ref(v_a_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2723_, lean_object* v_elems_2724_){
_start:
{
uint8_t v___x_2725_; 
lean_inc_ref(v_sep_2723_);
v___x_2725_ = lean_string_isempty(v_sep_2723_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = l_Lean_mkAtom(v_sep_2723_);
v___x_2727_ = l_Lean_mkSepArray(v_elems_2724_, v___x_2726_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec_ref(v_sep_2723_);
v___x_2728_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2729_ = l_Lean_mkSepArray(v_elems_2724_, v___x_2728_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2730_, lean_object* v_elems_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2730_, v_elems_2731_);
lean_dec_ref(v_elems_2731_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2733_, lean_object* v_toPure_2734_, lean_object* v_sep_2735_, lean_object* v_ref_2736_){
_start:
{
lean_object* v___y_2738_; uint8_t v___x_2741_; 
lean_inc_ref(v_sep_2735_);
v___x_2741_ = lean_string_isempty(v_sep_2735_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_mkAtomFrom(v_ref_2736_, v_sep_2735_, v___x_2741_);
v___y_2738_ = v___x_2742_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2743_; 
lean_dec_ref(v_sep_2735_);
v___x_2743_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2738_ = v___x_2743_;
goto v___jp_2737_;
}
v___jp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = l_Lean_mkSepArray(v_elems_2733_, v___y_2738_);
v___x_2740_ = lean_apply_2(v_toPure_2734_, lean_box(0), v___x_2739_);
return v___x_2740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2744_, lean_object* v_toPure_2745_, lean_object* v_sep_2746_, lean_object* v_ref_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2744_, v_toPure_2745_, v_sep_2746_, v_ref_2747_);
lean_dec(v_ref_2747_);
lean_dec_ref(v_elems_2744_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_sep_2751_, lean_object* v_elems_2752_){
_start:
{
lean_object* v_toApplicative_2753_; lean_object* v_toBind_2754_; lean_object* v_getRef_2755_; lean_object* v_toPure_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; 
v_toApplicative_2753_ = lean_ctor_get(v_inst_2749_, 0);
lean_inc_ref(v_toApplicative_2753_);
v_toBind_2754_ = lean_ctor_get(v_inst_2749_, 1);
lean_inc(v_toBind_2754_);
lean_dec_ref(v_inst_2749_);
v_getRef_2755_ = lean_ctor_get(v_inst_2750_, 0);
lean_inc(v_getRef_2755_);
lean_dec_ref(v_inst_2750_);
v_toPure_2756_ = lean_ctor_get(v_toApplicative_2753_, 1);
lean_inc(v_toPure_2756_);
lean_dec_ref(v_toApplicative_2753_);
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2757_, 0, v_elems_2752_);
lean_closure_set(v___f_2757_, 1, v_toPure_2756_);
lean_closure_set(v___f_2757_, 2, v_sep_2751_);
v___x_2758_ = lean_apply_4(v_toBind_2754_, lean_box(0), lean_box(0), v_getRef_2755_, v___f_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_sep_2762_, lean_object* v_elems_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2760_, v_inst_2761_, v_sep_2762_, v_elems_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2765_, lean_object* v_elems_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2765_, v_elems_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2768_, lean_object* v_elems_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2768_, v_elems_2769_);
lean_dec_ref(v_elems_2769_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2771_, lean_object* v_sep_2772_, lean_object* v_elems_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2772_, v_elems_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2775_, lean_object* v_sep_2776_, lean_object* v_elems_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2775_, v_sep_2776_, v_elems_2777_);
lean_dec_ref(v_elems_2777_);
lean_dec(v_k_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2779_, lean_object* v_sep_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2781_, 0, v_k_2779_);
lean_closure_set(v___x_2781_, 1, v_sep_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2790_ = lean_array_get_size(v_x_2789_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_nat_dec_eq(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2793_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2794_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2795_ = lean_box(2);
v___x_2796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2794_);
lean_ctor_set(v___x_2796_, 2, v_x_2789_);
v___x_2797_ = lean_unsigned_to_nat(2u);
v___x_2798_ = lean_mk_empty_array_with_capacity(v___x_2797_);
v___x_2799_ = lean_array_push(v___x_2798_, v_fn_2788_);
v___x_2800_ = lean_array_push(v___x_2799_, v___x_2796_);
v___x_2801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2795_);
lean_ctor_set(v___x_2801_, 1, v___x_2793_);
lean_ctor_set(v___x_2801_, 2, v___x_2800_);
return v___x_2801_;
}
else
{
lean_dec_ref(v_x_2789_);
return v_fn_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2802_, lean_object* v_args_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = l_Lean_mkCIdent(v_fn_2802_);
v___x_2805_ = l_Lean_Syntax_mkApp(v___x_2804_, v_args_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2806_, lean_object* v_val_2807_, lean_object* v_info_2808_){
_start:
{
lean_object* v_atom_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_atom_2809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2809_, 0, v_info_2808_);
lean_ctor_set(v_atom_2809_, 1, v_val_2807_);
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = lean_mk_empty_array_with_capacity(v___x_2810_);
v___x_2812_ = lean_array_push(v___x_2811_, v_atom_2809_);
v___x_2813_ = lean_box(2);
v___x_2814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v_kind_2806_);
lean_ctor_set(v___x_2814_, 2, v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2818_, lean_object* v_info_2819_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2821_ = l_Char_quote(v_val_2818_);
v___x_2822_ = l_Lean_Syntax_mkLit(v___x_2820_, v___x_2821_, v_info_2819_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2823_, lean_object* v_info_2824_){
_start:
{
uint32_t v_val_boxed_2825_; lean_object* v_res_2826_; 
v_val_boxed_2825_ = lean_unbox_uint32(v_val_2823_);
lean_dec(v_val_2823_);
v_res_2826_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2825_, v_info_2824_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2830_, lean_object* v_info_2831_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2832_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2833_ = l_String_quote(v_val_2830_);
v___x_2834_ = l_Lean_Syntax_mkLit(v___x_2832_, v___x_2833_, v_info_2831_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2838_, lean_object* v_info_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2841_ = l_Lean_Syntax_mkLit(v___x_2840_, v_val_2838_, v_info_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2842_, lean_object* v_info_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2845_ = l_Nat_reprFast(v_val_2842_);
v___x_2846_ = l_Lean_Syntax_mkLit(v___x_2844_, v___x_2845_, v_info_2843_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2850_, lean_object* v_info_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2853_ = l_Lean_Syntax_mkLit(v___x_2852_, v_val_2850_, v_info_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2857_, lean_object* v_info_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2860_ = l_Lean_Syntax_mkLit(v___x_2859_, v_val_2857_, v_info_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2861_, lean_object* v_i_2862_, lean_object* v_val_2863_){
_start:
{
uint8_t v___x_2864_; 
v___x_2864_ = lean_string_utf8_at_end(v_s_2861_, v_i_2862_);
if (v___x_2864_ == 0)
{
uint32_t v_c_2865_; uint32_t v___x_2866_; uint8_t v___x_2867_; 
v_c_2865_ = lean_string_utf8_get(v_s_2861_, v_i_2862_);
v___x_2866_ = 48;
v___x_2867_ = lean_uint32_dec_eq(v_c_2865_, v___x_2866_);
if (v___x_2867_ == 0)
{
uint32_t v___x_2868_; uint8_t v___x_2869_; 
v___x_2868_ = 49;
v___x_2869_ = lean_uint32_dec_eq(v_c_2865_, v___x_2868_);
if (v___x_2869_ == 0)
{
uint32_t v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = 95;
v___x_2871_ = lean_uint32_dec_eq(v_c_2865_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec(v_val_2863_);
lean_dec(v_i_2862_);
v___x_2872_ = lean_box(0);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_string_utf8_next(v_s_2861_, v_i_2862_);
lean_dec(v_i_2862_);
v_i_2862_ = v___x_2873_;
goto _start;
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2875_ = lean_string_utf8_next(v_s_2861_, v_i_2862_);
lean_dec(v_i_2862_);
v___x_2876_ = lean_unsigned_to_nat(2u);
v___x_2877_ = lean_nat_mul(v___x_2876_, v_val_2863_);
lean_dec(v_val_2863_);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_nat_add(v___x_2877_, v___x_2878_);
lean_dec(v___x_2877_);
v_i_2862_ = v___x_2875_;
v_val_2863_ = v___x_2879_;
goto _start;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_string_utf8_next(v_s_2861_, v_i_2862_);
lean_dec(v_i_2862_);
v___x_2882_ = lean_unsigned_to_nat(2u);
v___x_2883_ = lean_nat_mul(v___x_2882_, v_val_2863_);
lean_dec(v_val_2863_);
v_i_2862_ = v___x_2881_;
v_val_2863_ = v___x_2883_;
goto _start;
}
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_i_2862_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_val_2863_);
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2886_, lean_object* v_i_2887_, lean_object* v_val_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2886_, v_i_2887_, v_val_2888_);
lean_dec_ref(v_s_2886_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2890_, lean_object* v_i_2891_, lean_object* v_val_2892_){
_start:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_string_utf8_at_end(v_s_2890_, v_i_2891_);
if (v___x_2893_ == 0)
{
uint32_t v_c_2894_; uint8_t v___y_2896_; uint32_t v___x_2910_; uint8_t v___x_2911_; 
v_c_2894_ = lean_string_utf8_get(v_s_2890_, v_i_2891_);
v___x_2910_ = 48;
v___x_2911_ = lean_uint32_dec_le(v___x_2910_, v_c_2894_);
if (v___x_2911_ == 0)
{
v___y_2896_ = v___x_2893_;
goto v___jp_2895_;
}
else
{
uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = 55;
v___x_2913_ = lean_uint32_dec_le(v_c_2894_, v___x_2912_);
v___y_2896_ = v___x_2913_;
goto v___jp_2895_;
}
v___jp_2895_:
{
if (v___y_2896_ == 0)
{
uint32_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = 95;
v___x_2898_ = lean_uint32_dec_eq(v_c_2894_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_val_2892_);
lean_dec(v_i_2891_);
v___x_2899_ = lean_box(0);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_string_utf8_next(v_s_2890_, v_i_2891_);
lean_dec(v_i_2891_);
v_i_2891_ = v___x_2900_;
goto _start;
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2902_ = lean_string_utf8_next(v_s_2890_, v_i_2891_);
lean_dec(v_i_2891_);
v___x_2903_ = lean_unsigned_to_nat(8u);
v___x_2904_ = lean_nat_mul(v___x_2903_, v_val_2892_);
lean_dec(v_val_2892_);
v___x_2905_ = lean_uint32_to_nat(v_c_2894_);
v___x_2906_ = lean_nat_add(v___x_2904_, v___x_2905_);
lean_dec(v___x_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_unsigned_to_nat(48u);
v___x_2908_ = lean_nat_sub(v___x_2906_, v___x_2907_);
lean_dec(v___x_2906_);
v_i_2891_ = v___x_2902_;
v_val_2892_ = v___x_2908_;
goto _start;
}
}
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_i_2891_);
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_val_2892_);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2915_, lean_object* v_i_2916_, lean_object* v_val_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2915_, v_i_2916_, v_val_2917_);
lean_dec_ref(v_s_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2919_, lean_object* v_i_2920_){
_start:
{
uint32_t v_c_2921_; lean_object* v_i_2922_; uint32_t v___x_2949_; uint8_t v___x_2950_; 
v_c_2921_ = lean_string_utf8_get(v_s_2919_, v_i_2920_);
v_i_2922_ = lean_string_utf8_next(v_s_2919_, v_i_2920_);
v___x_2949_ = 48;
v___x_2950_ = lean_uint32_dec_le(v___x_2949_, v_c_2921_);
if (v___x_2950_ == 0)
{
goto v___jp_2937_;
}
else
{
uint32_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = 57;
v___x_2952_ = lean_uint32_dec_le(v_c_2921_, v___x_2951_);
if (v___x_2952_ == 0)
{
goto v___jp_2937_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2953_ = lean_uint32_to_nat(v_c_2921_);
v___x_2954_ = lean_unsigned_to_nat(48u);
v___x_2955_ = lean_nat_sub(v___x_2953_, v___x_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v_i_2922_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
v___jp_2923_:
{
uint32_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = 65;
v___x_2925_ = lean_uint32_dec_le(v___x_2924_, v_c_2921_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v_i_2922_);
v___x_2926_ = lean_box(0);
return v___x_2926_;
}
else
{
uint32_t v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = 70;
v___x_2928_ = lean_uint32_dec_le(v_c_2921_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
lean_dec(v_i_2922_);
v___x_2929_ = lean_box(0);
return v___x_2929_;
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2930_ = lean_unsigned_to_nat(10u);
v___x_2931_ = lean_uint32_to_nat(v_c_2921_);
v___x_2932_ = lean_nat_add(v___x_2930_, v___x_2931_);
lean_dec(v___x_2931_);
v___x_2933_ = lean_unsigned_to_nat(65u);
v___x_2934_ = lean_nat_sub(v___x_2932_, v___x_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v_i_2922_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
}
v___jp_2937_:
{
uint32_t v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = 97;
v___x_2939_ = lean_uint32_dec_le(v___x_2938_, v_c_2921_);
if (v___x_2939_ == 0)
{
goto v___jp_2923_;
}
else
{
uint32_t v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = 102;
v___x_2941_ = lean_uint32_dec_le(v_c_2921_, v___x_2940_);
if (v___x_2941_ == 0)
{
goto v___jp_2923_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2942_ = lean_unsigned_to_nat(10u);
v___x_2943_ = lean_uint32_to_nat(v_c_2921_);
v___x_2944_ = lean_nat_add(v___x_2942_, v___x_2943_);
lean_dec(v___x_2943_);
v___x_2945_ = lean_unsigned_to_nat(97u);
v___x_2946_ = lean_nat_sub(v___x_2944_, v___x_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v_i_2922_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2958_, lean_object* v_i_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2958_, v_i_2959_);
lean_dec(v_i_2959_);
lean_dec_ref(v_s_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2961_, lean_object* v_i_2962_, lean_object* v_val_2963_){
_start:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_string_utf8_at_end(v_s_2961_, v_i_2962_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2961_, v_i_2962_);
if (lean_obj_tag(v___x_2965_) == 0)
{
uint32_t v___x_2966_; uint32_t v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = lean_string_utf8_get(v_s_2961_, v_i_2962_);
v___x_2967_ = 95;
v___x_2968_ = lean_uint32_dec_eq(v___x_2966_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; 
lean_dec(v_val_2963_);
lean_dec(v_i_2962_);
v___x_2969_ = lean_box(0);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_string_utf8_next(v_s_2961_, v_i_2962_);
lean_dec(v_i_2962_);
v_i_2962_ = v___x_2970_;
goto _start;
}
}
else
{
lean_object* v_val_2972_; lean_object* v_fst_2973_; lean_object* v_snd_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec(v_i_2962_);
v_val_2972_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_val_2972_);
lean_dec_ref_known(v___x_2965_, 1);
v_fst_2973_ = lean_ctor_get(v_val_2972_, 0);
lean_inc(v_fst_2973_);
v_snd_2974_ = lean_ctor_get(v_val_2972_, 1);
lean_inc(v_snd_2974_);
lean_dec(v_val_2972_);
v___x_2975_ = lean_unsigned_to_nat(16u);
v___x_2976_ = lean_nat_mul(v___x_2975_, v_val_2963_);
lean_dec(v_val_2963_);
v___x_2977_ = lean_nat_add(v___x_2976_, v_fst_2973_);
lean_dec(v_fst_2973_);
lean_dec(v___x_2976_);
v_i_2962_ = v_snd_2974_;
v_val_2963_ = v___x_2977_;
goto _start;
}
}
else
{
lean_object* v___x_2979_; 
lean_dec(v_i_2962_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_val_2963_);
return v___x_2979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_2980_, lean_object* v_i_2981_, lean_object* v_val_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2980_, v_i_2981_, v_val_2982_);
lean_dec_ref(v_s_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_2984_, lean_object* v_i_2985_, lean_object* v_val_2986_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_string_utf8_at_end(v_s_2984_, v_i_2985_);
if (v___x_2987_ == 0)
{
uint32_t v_c_2988_; uint8_t v___y_2990_; uint32_t v___x_3004_; uint8_t v___x_3005_; 
v_c_2988_ = lean_string_utf8_get(v_s_2984_, v_i_2985_);
v___x_3004_ = 48;
v___x_3005_ = lean_uint32_dec_le(v___x_3004_, v_c_2988_);
if (v___x_3005_ == 0)
{
v___y_2990_ = v___x_2987_;
goto v___jp_2989_;
}
else
{
uint32_t v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = 57;
v___x_3007_ = lean_uint32_dec_le(v_c_2988_, v___x_3006_);
v___y_2990_ = v___x_3007_;
goto v___jp_2989_;
}
v___jp_2989_:
{
if (v___y_2990_ == 0)
{
uint32_t v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = 95;
v___x_2992_ = lean_uint32_dec_eq(v_c_2988_, v___x_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
lean_dec(v_val_2986_);
lean_dec(v_i_2985_);
v___x_2993_ = lean_box(0);
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_string_utf8_next(v_s_2984_, v_i_2985_);
lean_dec(v_i_2985_);
v_i_2985_ = v___x_2994_;
goto _start;
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2996_ = lean_string_utf8_next(v_s_2984_, v_i_2985_);
lean_dec(v_i_2985_);
v___x_2997_ = lean_unsigned_to_nat(10u);
v___x_2998_ = lean_nat_mul(v___x_2997_, v_val_2986_);
lean_dec(v_val_2986_);
v___x_2999_ = lean_uint32_to_nat(v_c_2988_);
v___x_3000_ = lean_nat_add(v___x_2998_, v___x_2999_);
lean_dec(v___x_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_unsigned_to_nat(48u);
v___x_3002_ = lean_nat_sub(v___x_3000_, v___x_3001_);
lean_dec(v___x_3000_);
v_i_2985_ = v___x_2996_;
v_val_2986_ = v___x_3002_;
goto _start;
}
}
}
else
{
lean_object* v___x_3008_; 
lean_dec(v_i_2985_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_val_2986_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3009_, lean_object* v_i_3010_, lean_object* v_val_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3009_, v_i_3010_, v_val_3011_);
lean_dec_ref(v_s_3009_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3015_){
_start:
{
lean_object* v_len_3016_; lean_object* v___x_3017_; uint8_t v___x_3027_; 
v_len_3016_ = lean_string_length(v_s_3015_);
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3027_ = lean_nat_dec_eq(v_len_3016_, v___x_3017_);
if (v___x_3027_ == 0)
{
uint32_t v_c_3028_; uint32_t v___x_3029_; uint8_t v___x_3030_; 
v_c_3028_ = lean_string_utf8_get(v_s_3015_, v___x_3017_);
v___x_3029_ = 48;
v___x_3030_ = lean_uint32_dec_eq(v_c_3028_, v___x_3029_);
if (v___x_3030_ == 0)
{
uint8_t v___x_3031_; 
lean_dec(v_len_3016_);
v___x_3031_ = lean_uint32_dec_le(v___x_3029_, v_c_3028_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_box(0);
return v___x_3032_;
}
else
{
uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = 57;
v___x_3034_ = lean_uint32_dec_le(v_c_3028_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_box(0);
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; 
v___x_3036_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3015_, v___x_3017_, v___x_3017_);
return v___x_3036_;
}
}
}
else
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_nat_dec_eq(v_len_3016_, v___x_3037_);
lean_dec(v_len_3016_);
if (v___x_3038_ == 0)
{
uint32_t v_c_3039_; uint32_t v___x_3040_; uint8_t v___x_3041_; 
v_c_3039_ = lean_string_utf8_get(v_s_3015_, v___x_3037_);
v___x_3040_ = 120;
v___x_3041_ = lean_uint32_dec_eq(v_c_3039_, v___x_3040_);
if (v___x_3041_ == 0)
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = 88;
v___x_3043_ = lean_uint32_dec_eq(v_c_3039_, v___x_3042_);
if (v___x_3043_ == 0)
{
uint32_t v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = 98;
v___x_3045_ = lean_uint32_dec_eq(v_c_3039_, v___x_3044_);
if (v___x_3045_ == 0)
{
uint32_t v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = 66;
v___x_3047_ = lean_uint32_dec_eq(v_c_3039_, v___x_3046_);
if (v___x_3047_ == 0)
{
uint32_t v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = 111;
v___x_3049_ = lean_uint32_dec_eq(v_c_3039_, v___x_3048_);
if (v___x_3049_ == 0)
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 79;
v___x_3051_ = lean_uint32_dec_eq(v_c_3039_, v___x_3050_);
if (v___x_3051_ == 0)
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_uint32_dec_le(v___x_3029_, v_c_3039_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_box(0);
return v___x_3053_;
}
else
{
uint32_t v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = 57;
v___x_3055_ = lean_uint32_dec_le(v_c_3039_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_box(0);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3015_, v___x_3017_, v___x_3017_);
return v___x_3057_;
}
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
goto v___jp_3021_;
}
}
else
{
goto v___jp_3021_;
}
}
else
{
goto v___jp_3024_;
}
}
else
{
goto v___jp_3024_;
}
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3058_;
}
}
}
else
{
lean_object* v___x_3059_; 
lean_dec(v_len_3016_);
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
v___jp_3018_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_unsigned_to_nat(2u);
v___x_3020_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3015_, v___x_3019_, v___x_3017_);
return v___x_3020_;
}
v___jp_3021_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_unsigned_to_nat(2u);
v___x_3023_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3015_, v___x_3022_, v___x_3017_);
return v___x_3023_;
}
v___jp_3024_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_unsigned_to_nat(2u);
v___x_3026_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3015_, v___x_3025_, v___x_3017_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3060_);
lean_dec_ref(v_s_3060_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3062_, lean_object* v_stx_3063_){
_start:
{
if (lean_obj_tag(v_stx_3063_) == 1)
{
lean_object* v_kind_3064_; lean_object* v_args_3065_; uint8_t v___y_3067_; uint8_t v___x_3074_; 
v_kind_3064_ = lean_ctor_get(v_stx_3063_, 1);
v_args_3065_ = lean_ctor_get(v_stx_3063_, 2);
v___x_3074_ = lean_name_eq(v_kind_3064_, v_litKind_3062_);
if (v___x_3074_ == 0)
{
v___y_3067_ = v___x_3074_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3075_ = lean_array_get_size(v_args_3065_);
v___x_3076_ = lean_unsigned_to_nat(1u);
v___x_3077_ = lean_nat_dec_eq(v___x_3075_, v___x_3076_);
v___y_3067_ = v___x_3077_;
goto v___jp_3066_;
}
v___jp_3066_:
{
if (v___y_3067_ == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_box(0);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_array_fget_borrowed(v_args_3065_, v___x_3069_);
if (lean_obj_tag(v___x_3070_) == 2)
{
lean_object* v_val_3071_; lean_object* v___x_3072_; 
v_val_3071_ = lean_ctor_get(v___x_3070_, 1);
lean_inc_ref(v_val_3071_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_val_3071_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_box(0);
return v___x_3073_;
}
}
}
}
else
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_box(0);
return v___x_3078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3079_, lean_object* v_stx_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Syntax_isLit_x3f(v_litKind_3079_, v_stx_3080_);
lean_dec(v_stx_3080_);
lean_dec(v_litKind_3079_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3082_, lean_object* v_stx_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Syntax_isLit_x3f(v_litKind_3082_, v_stx_3083_);
if (lean_obj_tag(v___x_3084_) == 1)
{
lean_object* v_val_3085_; lean_object* v___x_3086_; 
v_val_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_val_3085_);
lean_dec_ref_known(v___x_3084_, 1);
v___x_3086_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3085_);
lean_dec(v_val_3085_);
return v___x_3086_;
}
else
{
lean_object* v___x_3087_; 
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3088_, lean_object* v_stx_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3088_, v_stx_3089_);
lean_dec(v_stx_3089_);
lean_dec(v_litKind_3088_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3091_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3093_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3092_, v_s_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Syntax_isNatLit_x3f(v_s_3094_);
lean_dec(v_s_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3099_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3101_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3100_, v_s_3099_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3102_);
lean_dec(v_s_3102_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3104_, lean_object* v_i_3105_, lean_object* v_val_3106_, lean_object* v_e_3107_, uint8_t v_sign_3108_, lean_object* v_exp_3109_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_string_utf8_at_end(v_s_3104_, v_i_3105_);
if (v___x_3110_ == 0)
{
uint32_t v_c_3111_; uint8_t v___y_3113_; uint32_t v___x_3127_; uint8_t v___x_3128_; 
v_c_3111_ = lean_string_utf8_get(v_s_3104_, v_i_3105_);
v___x_3127_ = 48;
v___x_3128_ = lean_uint32_dec_le(v___x_3127_, v_c_3111_);
if (v___x_3128_ == 0)
{
v___y_3113_ = v___x_3110_;
goto v___jp_3112_;
}
else
{
uint32_t v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = 57;
v___x_3130_ = lean_uint32_dec_le(v_c_3111_, v___x_3129_);
v___y_3113_ = v___x_3130_;
goto v___jp_3112_;
}
v___jp_3112_:
{
if (v___y_3113_ == 0)
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 95;
v___x_3115_ = lean_uint32_dec_eq(v_c_3111_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
lean_dec(v_exp_3109_);
lean_dec(v_val_3106_);
lean_dec(v_i_3105_);
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = lean_string_utf8_next(v_s_3104_, v_i_3105_);
lean_dec(v_i_3105_);
v_i_3105_ = v___x_3117_;
goto _start;
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3119_ = lean_string_utf8_next(v_s_3104_, v_i_3105_);
lean_dec(v_i_3105_);
v___x_3120_ = lean_unsigned_to_nat(10u);
v___x_3121_ = lean_nat_mul(v___x_3120_, v_exp_3109_);
lean_dec(v_exp_3109_);
v___x_3122_ = lean_uint32_to_nat(v_c_3111_);
v___x_3123_ = lean_nat_add(v___x_3121_, v___x_3122_);
lean_dec(v___x_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_unsigned_to_nat(48u);
v___x_3125_ = lean_nat_sub(v___x_3123_, v___x_3124_);
lean_dec(v___x_3123_);
v_i_3105_ = v___x_3119_;
v_exp_3109_ = v___x_3125_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3105_);
if (v_sign_3108_ == 0)
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_nat_dec_le(v_e_3107_, v_exp_3109_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3132_ = lean_nat_sub(v_e_3107_, v_exp_3109_);
lean_dec(v_exp_3109_);
v___x_3133_ = lean_box(v___x_3110_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_val_3106_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3137_ = lean_nat_sub(v_exp_3109_, v_e_3107_);
lean_dec(v_exp_3109_);
v___x_3138_ = lean_box(v_sign_3108_);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v___x_3137_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_val_3106_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3142_ = lean_nat_add(v_exp_3109_, v_e_3107_);
lean_dec(v_exp_3109_);
v___x_3143_ = lean_box(v_sign_3108_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3142_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_val_3106_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3147_, lean_object* v_i_3148_, lean_object* v_val_3149_, lean_object* v_e_3150_, lean_object* v_sign_3151_, lean_object* v_exp_3152_){
_start:
{
uint8_t v_sign_boxed_3153_; lean_object* v_res_3154_; 
v_sign_boxed_3153_ = lean_unbox(v_sign_3151_);
v_res_3154_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3147_, v_i_3148_, v_val_3149_, v_e_3150_, v_sign_boxed_3153_, v_exp_3152_);
lean_dec(v_e_3150_);
lean_dec_ref(v_s_3147_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3155_, lean_object* v_i_3156_, lean_object* v_val_3157_, lean_object* v_e_3158_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = lean_string_utf8_at_end(v_s_3155_, v_i_3156_);
if (v___x_3159_ == 0)
{
uint32_t v_c_3160_; uint32_t v___x_3161_; uint8_t v___x_3162_; 
v_c_3160_ = lean_string_utf8_get(v_s_3155_, v_i_3156_);
v___x_3161_ = 45;
v___x_3162_ = lean_uint32_dec_eq(v_c_3160_, v___x_3161_);
if (v___x_3162_ == 0)
{
uint32_t v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = 43;
v___x_3164_ = lean_uint32_dec_eq(v_c_3160_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3155_, v_i_3156_, v_val_3157_, v_e_3158_, v___x_3164_, v___x_3165_);
return v___x_3166_;
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_string_utf8_next(v_s_3155_, v_i_3156_);
lean_dec(v_i_3156_);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3155_, v___x_3167_, v_val_3157_, v_e_3158_, v___x_3162_, v___x_3168_);
return v___x_3169_;
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = lean_string_utf8_next(v_s_3155_, v_i_3156_);
lean_dec(v_i_3156_);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3155_, v___x_3170_, v_val_3157_, v_e_3158_, v___x_3162_, v___x_3171_);
return v___x_3172_;
}
}
else
{
lean_object* v___x_3173_; 
lean_dec(v_val_3157_);
lean_dec(v_i_3156_);
v___x_3173_ = lean_box(0);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3174_, lean_object* v_i_3175_, lean_object* v_val_3176_, lean_object* v_e_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3174_, v_i_3175_, v_val_3176_, v_e_3177_);
lean_dec(v_e_3177_);
lean_dec_ref(v_s_3174_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3179_, lean_object* v_i_3180_, lean_object* v_val_3181_, lean_object* v_e_3182_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_string_utf8_at_end(v_s_3179_, v_i_3180_);
if (v___x_3186_ == 0)
{
uint32_t v_c_3187_; uint8_t v___y_3189_; uint32_t v___x_3209_; uint8_t v___x_3210_; 
v_c_3187_ = lean_string_utf8_get(v_s_3179_, v_i_3180_);
v___x_3209_ = 48;
v___x_3210_ = lean_uint32_dec_le(v___x_3209_, v_c_3187_);
if (v___x_3210_ == 0)
{
v___y_3189_ = v___x_3186_;
goto v___jp_3188_;
}
else
{
uint32_t v___x_3211_; uint8_t v___x_3212_; 
v___x_3211_ = 57;
v___x_3212_ = lean_uint32_dec_le(v_c_3187_, v___x_3211_);
v___y_3189_ = v___x_3212_;
goto v___jp_3188_;
}
v___jp_3188_:
{
if (v___y_3189_ == 0)
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 95;
v___x_3191_ = lean_uint32_dec_eq(v_c_3187_, v___x_3190_);
if (v___x_3191_ == 0)
{
uint32_t v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = 101;
v___x_3193_ = lean_uint32_dec_eq(v_c_3187_, v___x_3192_);
if (v___x_3193_ == 0)
{
uint32_t v___x_3194_; uint8_t v___x_3195_; 
v___x_3194_ = 69;
v___x_3195_ = lean_uint32_dec_eq(v_c_3187_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
lean_dec(v_e_3182_);
lean_dec(v_val_3181_);
lean_dec(v_i_3180_);
v___x_3196_ = lean_box(0);
return v___x_3196_;
}
else
{
goto v___jp_3183_;
}
}
else
{
goto v___jp_3183_;
}
}
else
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_string_utf8_next(v_s_3179_, v_i_3180_);
lean_dec(v_i_3180_);
v_i_3180_ = v___x_3197_;
goto _start;
}
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3199_ = lean_string_utf8_next(v_s_3179_, v_i_3180_);
lean_dec(v_i_3180_);
v___x_3200_ = lean_unsigned_to_nat(10u);
v___x_3201_ = lean_nat_mul(v___x_3200_, v_val_3181_);
lean_dec(v_val_3181_);
v___x_3202_ = lean_uint32_to_nat(v_c_3187_);
v___x_3203_ = lean_nat_add(v___x_3201_, v___x_3202_);
lean_dec(v___x_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_unsigned_to_nat(48u);
v___x_3205_ = lean_nat_sub(v___x_3203_, v___x_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_unsigned_to_nat(1u);
v___x_3207_ = lean_nat_add(v_e_3182_, v___x_3206_);
lean_dec(v_e_3182_);
v_i_3180_ = v___x_3199_;
v_val_3181_ = v___x_3205_;
v_e_3182_ = v___x_3207_;
goto _start;
}
}
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v_i_3180_);
v___x_3213_ = lean_box(v___x_3186_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v_e_3182_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_val_3181_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
v___jp_3183_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_string_utf8_next(v_s_3179_, v_i_3180_);
lean_dec(v_i_3180_);
v___x_3185_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3179_, v___x_3184_, v_val_3181_, v_e_3182_);
lean_dec(v_e_3182_);
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3217_, lean_object* v_i_3218_, lean_object* v_val_3219_, lean_object* v_e_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3217_, v_i_3218_, v_val_3219_, v_e_3220_);
lean_dec_ref(v_s_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3222_, lean_object* v_i_3223_, lean_object* v_val_3224_){
_start:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_string_utf8_at_end(v_s_3222_, v_i_3223_);
if (v___x_3229_ == 0)
{
uint32_t v_c_3230_; uint8_t v___y_3232_; uint32_t v___x_3255_; uint8_t v___x_3256_; 
v_c_3230_ = lean_string_utf8_get(v_s_3222_, v_i_3223_);
v___x_3255_ = 48;
v___x_3256_ = lean_uint32_dec_le(v___x_3255_, v_c_3230_);
if (v___x_3256_ == 0)
{
v___y_3232_ = v___x_3229_;
goto v___jp_3231_;
}
else
{
uint32_t v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = 57;
v___x_3258_ = lean_uint32_dec_le(v_c_3230_, v___x_3257_);
v___y_3232_ = v___x_3258_;
goto v___jp_3231_;
}
v___jp_3231_:
{
if (v___y_3232_ == 0)
{
uint32_t v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = 95;
v___x_3234_ = lean_uint32_dec_eq(v_c_3230_, v___x_3233_);
if (v___x_3234_ == 0)
{
uint32_t v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = 46;
v___x_3236_ = lean_uint32_dec_eq(v_c_3230_, v___x_3235_);
if (v___x_3236_ == 0)
{
uint32_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = 101;
v___x_3238_ = lean_uint32_dec_eq(v_c_3230_, v___x_3237_);
if (v___x_3238_ == 0)
{
uint32_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = 69;
v___x_3240_ = lean_uint32_dec_eq(v_c_3230_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
lean_dec(v_val_3224_);
lean_dec(v_i_3223_);
v___x_3241_ = lean_box(0);
return v___x_3241_;
}
else
{
goto v___jp_3225_;
}
}
else
{
goto v___jp_3225_;
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_string_utf8_next(v_s_3222_, v_i_3223_);
lean_dec(v_i_3223_);
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3222_, v___x_3242_, v_val_3224_, v___x_3243_);
return v___x_3244_;
}
}
else
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_string_utf8_next(v_s_3222_, v_i_3223_);
lean_dec(v_i_3223_);
v_i_3223_ = v___x_3245_;
goto _start;
}
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3247_ = lean_string_utf8_next(v_s_3222_, v_i_3223_);
lean_dec(v_i_3223_);
v___x_3248_ = lean_unsigned_to_nat(10u);
v___x_3249_ = lean_nat_mul(v___x_3248_, v_val_3224_);
lean_dec(v_val_3224_);
v___x_3250_ = lean_uint32_to_nat(v_c_3230_);
v___x_3251_ = lean_nat_add(v___x_3249_, v___x_3250_);
lean_dec(v___x_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_unsigned_to_nat(48u);
v___x_3253_ = lean_nat_sub(v___x_3251_, v___x_3252_);
lean_dec(v___x_3251_);
v_i_3223_ = v___x_3247_;
v_val_3224_ = v___x_3253_;
goto _start;
}
}
}
else
{
lean_object* v___x_3259_; 
lean_dec(v_val_3224_);
lean_dec(v_i_3223_);
v___x_3259_ = lean_box(0);
return v___x_3259_;
}
v___jp_3225_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_string_utf8_next(v_s_3222_, v_i_3223_);
lean_dec(v_i_3223_);
v___x_3227_ = lean_unsigned_to_nat(0u);
v___x_3228_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3222_, v___x_3226_, v_val_3224_, v___x_3227_);
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3260_, lean_object* v_i_3261_, lean_object* v_val_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3260_, v_i_3261_, v_val_3262_);
lean_dec_ref(v_s_3260_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3264_){
_start:
{
lean_object* v_len_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v_len_3265_ = lean_string_length(v_s_3264_);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_nat_dec_eq(v_len_3265_, v___x_3266_);
lean_dec(v_len_3265_);
if (v___x_3267_ == 0)
{
uint32_t v_c_3268_; uint32_t v___x_3269_; uint8_t v___x_3270_; 
v_c_3268_ = lean_string_utf8_get(v_s_3264_, v___x_3266_);
v___x_3269_ = 48;
v___x_3270_ = lean_uint32_dec_le(v___x_3269_, v_c_3268_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_box(0);
return v___x_3271_;
}
else
{
uint32_t v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = 57;
v___x_3273_ = lean_uint32_dec_le(v_c_3268_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_box(0);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; 
v___x_3275_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3264_, v___x_3266_, v___x_3266_);
return v___x_3275_;
}
}
}
else
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_box(0);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3277_);
lean_dec_ref(v_s_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3281_ = l_Lean_Syntax_isLit_x3f(v___x_3280_, v_stx_3279_);
if (lean_obj_tag(v___x_3281_) == 1)
{
lean_object* v_val_3282_; lean_object* v___x_3283_; 
v_val_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3283_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3282_);
lean_dec(v_val_3282_);
return v___x_3283_;
}
else
{
lean_object* v___x_3284_; 
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
return v___x_3284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3285_);
lean_dec(v_stx_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3287_){
_start:
{
switch(lean_obj_tag(v_x_3287_))
{
case 2:
{
lean_object* v_val_3288_; lean_object* v___x_3289_; 
v_val_3288_ = lean_ctor_get(v_x_3287_, 1);
lean_inc_ref(v_val_3288_);
lean_dec_ref_known(v_x_3287_, 2);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v_val_3288_);
return v___x_3289_;
}
case 3:
{
lean_object* v_rawVal_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_rawVal_3290_ = lean_ctor_get(v_x_3287_, 1);
lean_inc_ref(v_rawVal_3290_);
lean_dec_ref_known(v_x_3287_, 4);
v___x_3291_ = lean_substring_tostring(v_rawVal_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
default: 
{
lean_object* v___x_3293_; 
lean_dec(v_x_3287_);
v___x_3293_ = lean_box(0);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3294_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
return v___x_3296_;
}
else
{
lean_object* v_val_3297_; 
v_val_3297_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v___x_3295_, 1);
return v_val_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Syntax_toNat(v_stx_3298_);
lean_dec(v_stx_3298_);
return v_res_3299_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = 9;
v___x_3301_ = lean_box_uint32(v___x_3300_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = 10;
v___x_3303_ = lean_box_uint32(v___x_3302_);
return v___x_3303_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = 13;
v___x_3305_ = lean_box_uint32(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = 39;
v___x_3307_ = lean_box_uint32(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = 34;
v___x_3309_ = lean_box_uint32(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = 92;
v___x_3311_ = lean_box_uint32(v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3312_, lean_object* v_i_3313_){
_start:
{
uint32_t v_c_3314_; lean_object* v_i_3315_; uint32_t v___x_3316_; uint8_t v___x_3317_; 
v_c_3314_ = lean_string_utf8_get(v_s_3312_, v_i_3313_);
v_i_3315_ = lean_string_utf8_next(v_s_3312_, v_i_3313_);
v___x_3316_ = 92;
v___x_3317_ = lean_uint32_dec_eq(v_c_3314_, v___x_3316_);
if (v___x_3317_ == 0)
{
uint32_t v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = 34;
v___x_3319_ = lean_uint32_dec_eq(v_c_3314_, v___x_3318_);
if (v___x_3319_ == 0)
{
uint32_t v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = 39;
v___x_3321_ = lean_uint32_dec_eq(v_c_3314_, v___x_3320_);
if (v___x_3321_ == 0)
{
uint32_t v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = 114;
v___x_3323_ = lean_uint32_dec_eq(v_c_3314_, v___x_3322_);
if (v___x_3323_ == 0)
{
uint32_t v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = 110;
v___x_3325_ = lean_uint32_dec_eq(v_c_3314_, v___x_3324_);
if (v___x_3325_ == 0)
{
uint32_t v___x_3326_; uint8_t v___x_3327_; 
v___x_3326_ = 116;
v___x_3327_ = lean_uint32_dec_eq(v_c_3314_, v___x_3326_);
if (v___x_3327_ == 0)
{
uint32_t v___x_3328_; uint8_t v___x_3329_; 
v___x_3328_ = 120;
v___x_3329_ = lean_uint32_dec_eq(v_c_3314_, v___x_3328_);
if (v___x_3329_ == 0)
{
uint32_t v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = 117;
v___x_3331_ = lean_uint32_dec_eq(v_c_3314_, v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
lean_dec(v_i_3315_);
v___x_3332_ = lean_box(0);
return v___x_3332_;
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3312_, v_i_3315_);
lean_dec(v_i_3315_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; 
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
v___x_3338_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3312_, v_snd_3337_);
lean_dec(v_snd_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; 
lean_dec(v_fst_3336_);
v___x_3339_ = lean_box(0);
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; lean_object* v_fst_3341_; lean_object* v_snd_3342_; lean_object* v___x_3343_; 
v_val_3340_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3338_, 1);
v_fst_3341_ = lean_ctor_get(v_val_3340_, 0);
lean_inc(v_fst_3341_);
v_snd_3342_ = lean_ctor_get(v_val_3340_, 1);
lean_inc(v_snd_3342_);
lean_dec(v_val_3340_);
v___x_3343_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3312_, v_snd_3342_);
lean_dec(v_snd_3342_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec(v_fst_3341_);
lean_dec(v_fst_3336_);
v___x_3344_ = lean_box(0);
return v___x_3344_;
}
else
{
lean_object* v_val_3345_; lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v___x_3348_; 
v_val_3345_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___x_3343_, 1);
v_fst_3346_ = lean_ctor_get(v_val_3345_, 0);
lean_inc(v_fst_3346_);
v_snd_3347_ = lean_ctor_get(v_val_3345_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_val_3345_);
v___x_3348_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3312_, v_snd_3347_);
lean_dec(v_snd_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_fst_3346_);
lean_dec(v_fst_3341_);
lean_dec(v_fst_3336_);
v___x_3349_ = lean_box(0);
return v___x_3349_;
}
else
{
lean_object* v_val_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3375_; 
v_val_3350_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3352_ = v___x_3348_;
v_isShared_3353_ = v_isSharedCheck_3375_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_val_3350_);
lean_dec(v___x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3375_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_fst_3354_; lean_object* v_snd_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3374_; 
v_fst_3354_ = lean_ctor_get(v_val_3350_, 0);
v_snd_3355_ = lean_ctor_get(v_val_3350_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_val_3350_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3357_ = v_val_3350_;
v_isShared_3358_ = v_isSharedCheck_3374_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_snd_3355_);
lean_inc(v_fst_3354_);
lean_dec(v_val_3350_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3374_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint32_t v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3359_ = lean_unsigned_to_nat(16u);
v___x_3360_ = lean_nat_mul(v___x_3359_, v_fst_3336_);
lean_dec(v_fst_3336_);
v___x_3361_ = lean_nat_add(v___x_3360_, v_fst_3341_);
lean_dec(v_fst_3341_);
lean_dec(v___x_3360_);
v___x_3362_ = lean_nat_mul(v___x_3359_, v___x_3361_);
lean_dec(v___x_3361_);
v___x_3363_ = lean_nat_add(v___x_3362_, v_fst_3346_);
lean_dec(v_fst_3346_);
lean_dec(v___x_3362_);
v___x_3364_ = lean_nat_mul(v___x_3359_, v___x_3363_);
lean_dec(v___x_3363_);
v___x_3365_ = lean_nat_add(v___x_3364_, v_fst_3354_);
lean_dec(v_fst_3354_);
lean_dec(v___x_3364_);
v___x_3366_ = l_Char_ofNat(v___x_3365_);
lean_dec(v___x_3365_);
v___x_3367_ = lean_box_uint32(v___x_3366_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3367_);
v___x_3369_ = v___x_3357_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_snd_3355_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3369_);
v___x_3371_ = v___x_3352_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
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
lean_object* v___x_3376_; 
v___x_3376_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3312_, v_i_3315_);
lean_dec(v_i_3315_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_box(0);
return v___x_3377_;
}
else
{
lean_object* v_val_3378_; lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3381_; 
v_val_3378_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_val_3378_);
lean_dec_ref_known(v___x_3376_, 1);
v_fst_3379_ = lean_ctor_get(v_val_3378_, 0);
lean_inc(v_fst_3379_);
v_snd_3380_ = lean_ctor_get(v_val_3378_, 1);
lean_inc(v_snd_3380_);
lean_dec(v_val_3378_);
v___x_3381_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3312_, v_snd_3380_);
lean_dec(v_snd_3380_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v___x_3382_; 
lean_dec(v_fst_3379_);
v___x_3382_ = lean_box(0);
return v___x_3382_;
}
else
{
lean_object* v_val_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3404_; 
v_val_3383_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3385_ = v___x_3381_;
v_isShared_3386_ = v_isSharedCheck_3404_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_val_3383_);
lean_dec(v___x_3381_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3404_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_fst_3387_; lean_object* v_snd_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3403_; 
v_fst_3387_ = lean_ctor_get(v_val_3383_, 0);
v_snd_3388_ = lean_ctor_get(v_val_3383_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_val_3383_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3390_ = v_val_3383_;
v_isShared_3391_ = v_isSharedCheck_3403_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_snd_3388_);
lean_inc(v_fst_3387_);
lean_dec(v_val_3383_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3403_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint32_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3392_ = lean_unsigned_to_nat(16u);
v___x_3393_ = lean_nat_mul(v___x_3392_, v_fst_3379_);
lean_dec(v_fst_3379_);
v___x_3394_ = lean_nat_add(v___x_3393_, v_fst_3387_);
lean_dec(v_fst_3387_);
lean_dec(v___x_3393_);
v___x_3395_ = l_Char_ofNat(v___x_3394_);
lean_dec(v___x_3394_);
v___x_3396_ = lean_box_uint32(v___x_3395_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3396_);
v___x_3398_ = v___x_3390_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_snd_3388_);
v___x_3398_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; 
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3398_);
v___x_3400_ = v___x_3385_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
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
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v_i_3315_);
v___x_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
lean_ctor_set(v___x_3409_, 1, v_i_3315_);
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v_i_3315_);
v___x_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
return v___x_3413_;
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v_i_3315_);
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
}
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v_i_3315_);
v___x_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
return v___x_3419_;
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set(v___x_3421_, 1, v_i_3315_);
v___x_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3423_, lean_object* v_i_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_Syntax_decodeQuotedChar(v_s_3423_, v_i_3424_);
lean_dec(v_i_3424_);
lean_dec_ref(v_s_3423_);
return v_res_3425_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3426_){
_start:
{
uint32_t v___x_3427_; uint8_t v___x_3428_; 
v___x_3427_ = 32;
v___x_3428_ = lean_uint32_dec_eq(v___y_3426_, v___x_3427_);
if (v___x_3428_ == 0)
{
uint32_t v___x_3429_; uint8_t v___x_3430_; 
v___x_3429_ = 9;
v___x_3430_ = lean_uint32_dec_eq(v___y_3426_, v___x_3429_);
if (v___x_3430_ == 0)
{
uint32_t v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = 13;
v___x_3432_ = lean_uint32_dec_eq(v___y_3426_, v___x_3431_);
if (v___x_3432_ == 0)
{
uint32_t v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = 10;
v___x_3434_ = lean_uint32_dec_eq(v___y_3426_, v___x_3433_);
return v___x_3434_;
}
else
{
return v___x_3432_;
}
}
else
{
return v___x_3430_;
}
}
else
{
return v___x_3428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3435_){
_start:
{
uint32_t v___y_270__boxed_3436_; uint8_t v_res_3437_; lean_object* v_r_3438_; 
v___y_270__boxed_3436_ = lean_unbox_uint32(v___y_3435_);
lean_dec(v___y_3435_);
v_res_3437_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_270__boxed_3436_);
v_r_3438_ = lean_box(v_res_3437_);
return v_r_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3440_, lean_object* v_i_3441_){
_start:
{
lean_object* v___f_3442_; uint32_t v___x_3447_; uint32_t v___x_3448_; uint8_t v___x_3449_; 
v___f_3442_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3447_ = lean_string_utf8_get(v_s_3440_, v_i_3441_);
v___x_3448_ = 32;
v___x_3449_ = lean_uint32_dec_eq(v___x_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
uint32_t v___x_3450_; uint8_t v___x_3451_; 
v___x_3450_ = 9;
v___x_3451_ = lean_uint32_dec_eq(v___x_3447_, v___x_3450_);
if (v___x_3451_ == 0)
{
uint32_t v___x_3452_; uint8_t v___x_3453_; 
v___x_3452_ = 13;
v___x_3453_ = lean_uint32_dec_eq(v___x_3447_, v___x_3452_);
if (v___x_3453_ == 0)
{
uint32_t v___x_3454_; uint8_t v___x_3455_; 
v___x_3454_ = 10;
v___x_3455_ = lean_uint32_dec_eq(v___x_3447_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; 
lean_dec_ref(v_s_3440_);
v___x_3456_ = lean_box(0);
return v___x_3456_;
}
else
{
goto v___jp_3443_;
}
}
else
{
goto v___jp_3443_;
}
}
else
{
goto v___jp_3443_;
}
}
else
{
goto v___jp_3443_;
}
v___jp_3443_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_string_utf8_next(v_s_3440_, v_i_3441_);
v___x_3445_ = lean_string_nextwhile(v_s_3440_, v___f_3442_, v___x_3444_);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3457_, lean_object* v_i_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Syntax_decodeStringGap(v_s_3457_, v_i_3458_);
lean_dec(v_i_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3460_, lean_object* v_i_3461_, lean_object* v_acc_3462_){
_start:
{
uint32_t v_c_3463_; uint32_t v___x_3464_; uint8_t v___x_3465_; 
v_c_3463_ = lean_string_utf8_get(v_s_3460_, v_i_3461_);
v___x_3464_ = 34;
v___x_3465_ = lean_uint32_dec_eq(v_c_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
lean_object* v_i_3466_; uint8_t v___x_3467_; 
v_i_3466_ = lean_string_utf8_next(v_s_3460_, v_i_3461_);
lean_dec(v_i_3461_);
v___x_3467_ = lean_string_utf8_at_end(v_s_3460_, v_i_3466_);
if (v___x_3467_ == 0)
{
uint32_t v___x_3468_; uint8_t v___x_3469_; 
v___x_3468_ = 92;
v___x_3469_ = lean_uint32_dec_eq(v_c_3463_, v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = lean_string_push(v_acc_3462_, v_c_3463_);
v_i_3461_ = v_i_3466_;
v_acc_3462_ = v___x_3470_;
goto _start;
}
else
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_Syntax_decodeQuotedChar(v_s_3460_, v_i_3466_);
if (lean_obj_tag(v___x_3472_) == 1)
{
lean_object* v_val_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; uint32_t v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_i_3466_);
v_val_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_val_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v_fst_3474_ = lean_ctor_get(v_val_3473_, 0);
lean_inc(v_fst_3474_);
v_snd_3475_ = lean_ctor_get(v_val_3473_, 1);
lean_inc(v_snd_3475_);
lean_dec(v_val_3473_);
v___x_3476_ = lean_unbox_uint32(v_fst_3474_);
lean_dec(v_fst_3474_);
v___x_3477_ = lean_string_push(v_acc_3462_, v___x_3476_);
v_i_3461_ = v_snd_3475_;
v_acc_3462_ = v___x_3477_;
goto _start;
}
else
{
lean_object* v___x_3479_; 
lean_dec(v___x_3472_);
lean_inc_ref(v_s_3460_);
v___x_3479_ = l_Lean_Syntax_decodeStringGap(v_s_3460_, v_i_3466_);
lean_dec(v_i_3466_);
if (lean_obj_tag(v___x_3479_) == 1)
{
lean_object* v_val_3480_; 
v_val_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v_i_3461_ = v_val_3480_;
goto _start;
}
else
{
lean_object* v___x_3482_; 
lean_dec(v___x_3479_);
lean_dec_ref(v_acc_3462_);
lean_dec_ref(v_s_3460_);
v___x_3482_ = lean_box(0);
return v___x_3482_;
}
}
}
}
else
{
lean_object* v___x_3483_; 
lean_dec(v_i_3466_);
lean_dec_ref(v_acc_3462_);
lean_dec_ref(v_s_3460_);
v___x_3483_ = lean_box(0);
return v___x_3483_;
}
}
else
{
lean_object* v___x_3484_; 
lean_dec(v_i_3461_);
lean_dec_ref(v_s_3460_);
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_acc_3462_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3485_, lean_object* v_i_3486_, lean_object* v_num_3487_){
_start:
{
uint32_t v_c_3488_; lean_object* v_i_3489_; uint32_t v___x_3490_; uint8_t v___x_3491_; 
v_c_3488_ = lean_string_utf8_get(v_s_3485_, v_i_3486_);
v_i_3489_ = lean_string_utf8_next(v_s_3485_, v_i_3486_);
lean_dec(v_i_3486_);
v___x_3490_ = 35;
v___x_3491_ = lean_uint32_dec_eq(v_c_3488_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3492_ = lean_string_utf8_byte_size(v_s_3485_);
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_add(v_num_3487_, v___x_3493_);
lean_dec(v_num_3487_);
v___x_3495_ = lean_nat_sub(v___x_3492_, v___x_3494_);
lean_dec(v___x_3494_);
v___x_3496_ = lean_string_utf8_extract(v_s_3485_, v_i_3489_, v___x_3495_);
lean_dec(v___x_3495_);
lean_dec(v_i_3489_);
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_unsigned_to_nat(1u);
v___x_3498_ = lean_nat_add(v_num_3487_, v___x_3497_);
lean_dec(v_num_3487_);
v_i_3486_ = v_i_3489_;
v_num_3487_ = v___x_3498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3500_, lean_object* v_i_3501_, lean_object* v_num_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3500_, v_i_3501_, v_num_3502_);
lean_dec_ref(v_s_3500_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3504_){
_start:
{
lean_object* v___x_3505_; uint32_t v___x_3506_; uint32_t v___x_3507_; uint8_t v___x_3508_; 
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_string_utf8_get(v_s_3504_, v___x_3505_);
v___x_3507_ = 114;
v___x_3508_ = lean_uint32_dec_eq(v___x_3506_, v___x_3507_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_unsigned_to_nat(1u);
v___x_3510_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3511_ = l_Lean_Syntax_decodeStrLitAux(v_s_3504_, v___x_3509_, v___x_3510_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_unsigned_to_nat(1u);
v___x_3513_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3504_, v___x_3512_, v___x_3505_);
lean_dec_ref(v_s_3504_);
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3515_){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3517_ = l_Lean_Syntax_isLit_x3f(v___x_3516_, v_stx_3515_);
if (lean_obj_tag(v___x_3517_) == 1)
{
lean_object* v_val_3518_; lean_object* v___x_3519_; 
v_val_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_val_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = l_Lean_Syntax_decodeStrLit(v_val_3518_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; 
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3521_);
lean_dec(v_stx_3521_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3523_){
_start:
{
lean_object* v___x_3524_; uint32_t v_c_3525_; uint32_t v___x_3526_; uint8_t v___x_3527_; 
v___x_3524_ = lean_unsigned_to_nat(1u);
v_c_3525_ = lean_string_utf8_get(v_s_3523_, v___x_3524_);
v___x_3526_ = 92;
v___x_3527_ = lean_uint32_dec_eq(v_c_3525_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_box_uint32(v_c_3525_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_unsigned_to_nat(2u);
v___x_3531_ = l_Lean_Syntax_decodeQuotedChar(v_s_3523_, v___x_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_box(0);
return v___x_3532_;
}
else
{
lean_object* v_val_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3541_; 
v_val_3533_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3535_ = v___x_3531_;
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_val_3533_);
lean_dec(v___x_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_fst_3537_; lean_object* v___x_3539_; 
v_fst_3537_ = lean_ctor_get(v_val_3533_, 0);
lean_inc(v_fst_3537_);
lean_dec(v_val_3533_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v_fst_3537_);
v___x_3539_ = v___x_3535_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_fst_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Syntax_decodeCharLit(v_s_3542_);
lean_dec_ref(v_s_3542_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3544_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3546_ = l_Lean_Syntax_isLit_x3f(v___x_3545_, v_stx_3544_);
if (lean_obj_tag(v___x_3546_) == 1)
{
lean_object* v_val_3547_; lean_object* v___x_3548_; 
v_val_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_val_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = l_Lean_Syntax_decodeCharLit(v_val_3547_);
lean_dec(v_val_3547_);
return v___x_3548_;
}
else
{
lean_object* v___x_3549_; 
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3550_);
lean_dec(v_stx_3550_);
return v_res_3551_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3552_){
_start:
{
uint32_t v___x_3574_; uint8_t v___x_3575_; 
v___x_3574_ = 65;
v___x_3575_ = lean_uint32_dec_le(v___x_3574_, v___y_3552_);
if (v___x_3575_ == 0)
{
goto v___jp_3569_;
}
else
{
uint32_t v___x_3576_; uint8_t v___x_3577_; 
v___x_3576_ = 90;
v___x_3577_ = lean_uint32_dec_le(v___y_3552_, v___x_3576_);
if (v___x_3577_ == 0)
{
goto v___jp_3569_;
}
else
{
return v___x_3577_;
}
}
v___jp_3553_:
{
uint32_t v___x_3554_; uint8_t v___x_3555_; 
v___x_3554_ = 95;
v___x_3555_ = lean_uint32_dec_eq(v___y_3552_, v___x_3554_);
if (v___x_3555_ == 0)
{
uint32_t v___x_3556_; uint8_t v___x_3557_; 
v___x_3556_ = 39;
v___x_3557_ = lean_uint32_dec_eq(v___y_3552_, v___x_3556_);
if (v___x_3557_ == 0)
{
uint32_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = 33;
v___x_3559_ = lean_uint32_dec_eq(v___y_3552_, v___x_3558_);
if (v___x_3559_ == 0)
{
uint32_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = 63;
v___x_3561_ = lean_uint32_dec_eq(v___y_3552_, v___x_3560_);
if (v___x_3561_ == 0)
{
uint8_t v___x_3562_; 
v___x_3562_ = l_Lean_isLetterLike(v___y_3552_);
if (v___x_3562_ == 0)
{
uint8_t v___x_3563_; 
v___x_3563_ = l_Lean_isSubScriptAlnum(v___y_3552_);
return v___x_3563_;
}
else
{
return v___x_3562_;
}
}
else
{
return v___x_3561_;
}
}
else
{
return v___x_3559_;
}
}
else
{
return v___x_3557_;
}
}
else
{
return v___x_3555_;
}
}
v___jp_3564_:
{
uint32_t v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = 48;
v___x_3566_ = lean_uint32_dec_le(v___x_3565_, v___y_3552_);
if (v___x_3566_ == 0)
{
goto v___jp_3553_;
}
else
{
uint32_t v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = 57;
v___x_3568_ = lean_uint32_dec_le(v___y_3552_, v___x_3567_);
if (v___x_3568_ == 0)
{
goto v___jp_3553_;
}
else
{
return v___x_3568_;
}
}
}
v___jp_3569_:
{
uint32_t v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = 97;
v___x_3571_ = lean_uint32_dec_le(v___x_3570_, v___y_3552_);
if (v___x_3571_ == 0)
{
goto v___jp_3564_;
}
else
{
uint32_t v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = 122;
v___x_3573_ = lean_uint32_dec_le(v___y_3552_, v___x_3572_);
if (v___x_3573_ == 0)
{
goto v___jp_3564_;
}
else
{
return v___x_3573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3578_){
_start:
{
uint32_t v___y_496__boxed_3579_; uint8_t v_res_3580_; lean_object* v_r_3581_; 
v___y_496__boxed_3579_ = lean_unbox_uint32(v___y_3578_);
lean_dec(v___y_3578_);
v_res_3580_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_496__boxed_3579_);
v_r_3581_ = lean_box(v_res_3580_);
return v_r_3581_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3582_, uint32_t v___x_3583_, uint32_t v___y_3584_){
_start:
{
uint8_t v___x_3585_; 
v___x_3585_ = lean_uint32_dec_le(v___x_3582_, v___y_3584_);
if (v___x_3585_ == 0)
{
return v___x_3585_;
}
else
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_uint32_dec_le(v___y_3584_, v___x_3583_);
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3587_, lean_object* v___x_3588_, lean_object* v___y_3589_){
_start:
{
uint32_t v___x_549__boxed_3590_; uint32_t v___x_550__boxed_3591_; uint32_t v___y_551__boxed_3592_; uint8_t v_res_3593_; lean_object* v_r_3594_; 
v___x_549__boxed_3590_ = lean_unbox_uint32(v___x_3587_);
lean_dec(v___x_3587_);
v___x_550__boxed_3591_ = lean_unbox_uint32(v___x_3588_);
lean_dec(v___x_3588_);
v___y_551__boxed_3592_ = lean_unbox_uint32(v___y_3589_);
lean_dec(v___y_3589_);
v_res_3593_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_549__boxed_3590_, v___x_550__boxed_3591_, v___y_551__boxed_3592_);
v_r_3594_ = lean_box(v_res_3593_);
return v_r_3594_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3595_, uint8_t v___x_3596_, uint32_t v_x_3597_){
_start:
{
uint32_t v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = 187;
v___x_3599_ = lean_uint32_dec_eq(v_x_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
return v___x_3595_;
}
else
{
return v___x_3596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3600_, lean_object* v___x_3601_, lean_object* v_x_3602_){
_start:
{
uint8_t v___x_562__boxed_3603_; uint8_t v___x_563__boxed_3604_; uint32_t v_x_564__boxed_3605_; uint8_t v_res_3606_; lean_object* v_r_3607_; 
v___x_562__boxed_3603_ = lean_unbox(v___x_3600_);
v___x_563__boxed_3604_ = lean_unbox(v___x_3601_);
v_x_564__boxed_3605_ = lean_unbox_uint32(v_x_3602_);
lean_dec(v_x_3602_);
v_res_3606_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_562__boxed_3603_, v___x_563__boxed_3604_, v_x_564__boxed_3605_);
v_r_3607_ = lean_box(v_res_3606_);
return v_r_3607_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = 48;
v___x_3610_ = lean_box_uint32(v___x_3609_);
return v___x_3610_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = 57;
v___x_3612_ = lean_box_uint32(v___x_3611_);
return v___x_3612_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___f_3615_; 
v___x_3613_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3614_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3615_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3615_, 0, v___x_3613_);
lean_closure_set(v___f_3615_, 1, v___x_3614_);
return v___f_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3616_, lean_object* v_acc_3617_){
_start:
{
lean_object* v_ss_3619_; lean_object* v_acc_3620_; uint8_t v___x_3629_; 
lean_inc_ref(v_ss_3616_);
v___x_3629_ = lean_substring_isempty(v_ss_3616_);
if (v___x_3629_ == 0)
{
uint32_t v_curr_3630_; uint32_t v___x_3631_; uint8_t v___x_3632_; 
lean_inc_ref(v_ss_3616_);
v_curr_3630_ = lean_substring_front(v_ss_3616_);
v___x_3631_ = 171;
v___x_3632_ = lean_uint32_dec_eq(v_curr_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___f_3633_; uint32_t v___x_3669_; uint8_t v___x_3670_; 
v___f_3633_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3669_ = 65;
v___x_3670_ = lean_uint32_dec_le(v___x_3669_, v_curr_3630_);
if (v___x_3670_ == 0)
{
goto v___jp_3664_;
}
else
{
uint32_t v___x_3671_; uint8_t v___x_3672_; 
v___x_3671_ = 90;
v___x_3672_ = lean_uint32_dec_le(v_curr_3630_, v___x_3671_);
if (v___x_3672_ == 0)
{
goto v___jp_3664_;
}
else
{
goto v___jp_3634_;
}
}
v___jp_3634_:
{
lean_object* v_idPart_3635_; lean_object* v_startPos_3636_; lean_object* v_stopPos_3637_; lean_object* v_startPos_3638_; lean_object* v_stopPos_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
lean_inc_ref(v_ss_3616_);
v_idPart_3635_ = lean_substring_takewhile(v_ss_3616_, v___f_3633_);
v_startPos_3636_ = lean_ctor_get(v_idPart_3635_, 1);
v_stopPos_3637_ = lean_ctor_get(v_idPart_3635_, 2);
v_startPos_3638_ = lean_ctor_get(v_ss_3616_, 1);
v_stopPos_3639_ = lean_ctor_get(v_ss_3616_, 2);
v___x_3640_ = lean_nat_sub(v_stopPos_3637_, v_startPos_3636_);
v___x_3641_ = lean_nat_sub(v_stopPos_3639_, v_startPos_3638_);
v___x_3642_ = lean_substring_extract(v_ss_3616_, v___x_3640_, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3643_, 0, v_idPart_3635_);
lean_ctor_set(v___x_3643_, 1, v_acc_3617_);
v_ss_3619_ = v___x_3642_;
v_acc_3620_ = v___x_3643_;
goto v___jp_3618_;
}
v___jp_3644_:
{
uint32_t v___x_3645_; uint8_t v___x_3646_; 
v___x_3645_ = 95;
v___x_3646_ = lean_uint32_dec_eq(v_curr_3630_, v___x_3645_);
if (v___x_3646_ == 0)
{
uint8_t v___x_3647_; 
v___x_3647_ = l_Lean_isLetterLike(v_curr_3630_);
if (v___x_3647_ == 0)
{
uint32_t v___x_3648_; uint8_t v___x_3649_; 
v___x_3648_ = 48;
v___x_3649_ = lean_uint32_dec_le(v___x_3648_, v_curr_3630_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec(v_acc_3617_);
lean_dec_ref(v_ss_3616_);
v___x_3650_ = lean_box(0);
return v___x_3650_;
}
else
{
uint32_t v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = 57;
v___x_3652_ = lean_uint32_dec_le(v_curr_3630_, v___x_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
lean_dec(v_acc_3617_);
lean_dec_ref(v_ss_3616_);
v___x_3653_ = lean_box(0);
return v___x_3653_;
}
else
{
lean_object* v___f_3654_; lean_object* v_idPart_3655_; lean_object* v_startPos_3656_; lean_object* v_stopPos_3657_; lean_object* v_startPos_3658_; lean_object* v_stopPos_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___f_3654_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3616_);
v_idPart_3655_ = lean_substring_takewhile(v_ss_3616_, v___f_3654_);
v_startPos_3656_ = lean_ctor_get(v_idPart_3655_, 1);
v_stopPos_3657_ = lean_ctor_get(v_idPart_3655_, 2);
v_startPos_3658_ = lean_ctor_get(v_ss_3616_, 1);
v_stopPos_3659_ = lean_ctor_get(v_ss_3616_, 2);
v___x_3660_ = lean_nat_sub(v_stopPos_3657_, v_startPos_3656_);
v___x_3661_ = lean_nat_sub(v_stopPos_3659_, v_startPos_3658_);
v___x_3662_ = lean_substring_extract(v_ss_3616_, v___x_3660_, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_idPart_3655_);
lean_ctor_set(v___x_3663_, 1, v_acc_3617_);
v_ss_3619_ = v___x_3662_;
v_acc_3620_ = v___x_3663_;
goto v___jp_3618_;
}
}
}
else
{
goto v___jp_3634_;
}
}
else
{
goto v___jp_3634_;
}
}
v___jp_3664_:
{
uint32_t v___x_3665_; uint8_t v___x_3666_; 
v___x_3665_ = 97;
v___x_3666_ = lean_uint32_dec_le(v___x_3665_, v_curr_3630_);
if (v___x_3666_ == 0)
{
goto v___jp_3644_;
}
else
{
uint32_t v___x_3667_; uint8_t v___x_3668_; 
v___x_3667_ = 122;
v___x_3668_ = lean_uint32_dec_le(v_curr_3630_, v___x_3667_);
if (v___x_3668_ == 0)
{
goto v___jp_3644_;
}
else
{
goto v___jp_3634_;
}
}
}
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___f_3675_; lean_object* v_escapedPart_3676_; lean_object* v_str_3677_; lean_object* v_startPos_3678_; lean_object* v_stopPos_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3700_; 
v___x_3673_ = lean_box(v___x_3632_);
v___x_3674_ = lean_box(v___x_3629_);
v___f_3675_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3675_, 0, v___x_3673_);
lean_closure_set(v___f_3675_, 1, v___x_3674_);
lean_inc_ref(v_ss_3616_);
v_escapedPart_3676_ = lean_substring_takewhile(v_ss_3616_, v___f_3675_);
v_str_3677_ = lean_ctor_get(v_escapedPart_3676_, 0);
v_startPos_3678_ = lean_ctor_get(v_escapedPart_3676_, 1);
v_stopPos_3679_ = lean_ctor_get(v_escapedPart_3676_, 2);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_escapedPart_3676_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3681_ = v_escapedPart_3676_;
v_isShared_3682_ = v_isSharedCheck_3700_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_stopPos_3679_);
lean_inc(v_startPos_3678_);
lean_inc(v_str_3677_);
lean_dec(v_escapedPart_3676_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3700_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v_startPos_3683_; lean_object* v_stopPos_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v_escapedPart_3688_; 
v_startPos_3683_ = lean_ctor_get(v_ss_3616_, 1);
v_stopPos_3684_ = lean_ctor_get(v_ss_3616_, 2);
v___x_3685_ = lean_string_utf8_next(v_str_3677_, v_stopPos_3679_);
lean_dec(v_stopPos_3679_);
lean_inc(v_stopPos_3684_);
v___x_3686_ = lean_string_pos_min(v_stopPos_3684_, v___x_3685_);
lean_inc(v___x_3686_);
lean_inc(v_startPos_3678_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 2, v___x_3686_);
v_escapedPart_3688_ = v___x_3681_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_str_3677_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_startPos_3678_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v___x_3686_);
v_escapedPart_3688_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; uint32_t v___x_3691_; uint32_t v___x_3692_; uint8_t v___x_3693_; 
v___x_3689_ = lean_nat_sub(v___x_3686_, v_startPos_3678_);
lean_dec(v_startPos_3678_);
lean_dec(v___x_3686_);
lean_inc(v___x_3689_);
lean_inc_ref_n(v_escapedPart_3688_, 2);
v___x_3690_ = lean_substring_prev(v_escapedPart_3688_, v___x_3689_);
v___x_3691_ = lean_substring_get(v_escapedPart_3688_, v___x_3690_);
v___x_3692_ = 187;
v___x_3693_ = lean_uint32_dec_eq(v___x_3691_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; 
lean_dec(v___x_3689_);
lean_dec_ref(v_escapedPart_3688_);
lean_dec(v_acc_3617_);
lean_dec_ref(v_ss_3616_);
v___x_3694_ = lean_box(0);
return v___x_3694_;
}
else
{
if (v___x_3629_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3695_ = lean_nat_sub(v_stopPos_3684_, v_startPos_3683_);
v___x_3696_ = lean_substring_extract(v_ss_3616_, v___x_3689_, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_escapedPart_3688_);
lean_ctor_set(v___x_3697_, 1, v_acc_3617_);
v_ss_3619_ = v___x_3696_;
v_acc_3620_ = v___x_3697_;
goto v___jp_3618_;
}
else
{
lean_object* v___x_3698_; 
lean_dec(v___x_3689_);
lean_dec_ref(v_escapedPart_3688_);
lean_dec(v_acc_3617_);
lean_dec_ref(v_ss_3616_);
v___x_3698_ = lean_box(0);
return v___x_3698_;
}
}
}
}
}
}
else
{
lean_object* v___x_3701_; 
lean_dec(v_acc_3617_);
lean_dec_ref(v_ss_3616_);
v___x_3701_ = lean_box(0);
return v___x_3701_;
}
v___jp_3618_:
{
uint32_t v___x_3621_; uint32_t v___x_3622_; uint8_t v___x_3623_; 
lean_inc_ref(v_ss_3619_);
v___x_3621_ = lean_substring_front(v_ss_3619_);
v___x_3622_ = 46;
v___x_3623_ = lean_uint32_dec_eq(v___x_3621_, v___x_3622_);
if (v___x_3623_ == 0)
{
uint8_t v___x_3624_; 
v___x_3624_ = lean_substring_isempty(v_ss_3619_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; 
lean_dec(v_acc_3620_);
v___x_3625_ = lean_box(0);
return v___x_3625_;
}
else
{
return v_acc_3620_;
}
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_unsigned_to_nat(1u);
v___x_3627_ = lean_substring_drop(v_ss_3619_, v___x_3626_);
v_ss_3616_ = v___x_3627_;
v_acc_3617_ = v_acc_3620_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3702_){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_box(0);
v___x_3704_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3702_, v___x_3703_);
v___x_3705_ = l_List_reverse___redArg(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3709_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3710_ = lean_unsigned_to_nat(10u);
v___x_3711_ = lean_unsigned_to_nat(1253u);
v___x_3712_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3713_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3714_ = l_mkPanicMessageWithDecl(v___x_3713_, v___x_3712_, v___x_3711_, v___x_3710_, v___x_3709_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 0)
{
lean_inc(v_init_3715_);
return v_init_3715_;
}
else
{
lean_object* v_head_3717_; lean_object* v_tail_3718_; lean_object* v___x_3719_; lean_object* v_comp_3720_; uint32_t v___x_3721_; uint32_t v___x_3722_; uint8_t v___x_3723_; 
v_head_3717_ = lean_ctor_get(v_x_3716_, 0);
lean_inc(v_head_3717_);
v_tail_3718_ = lean_ctor_get(v_x_3716_, 1);
lean_inc(v_tail_3718_);
lean_dec_ref_known(v_x_3716_, 2);
v___x_3719_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3715_, v_tail_3718_);
v_comp_3720_ = lean_substring_tostring(v_head_3717_);
lean_inc_ref(v_comp_3720_);
v___x_3721_ = lean_string_front(v_comp_3720_);
v___x_3722_ = 171;
v___x_3723_ = lean_uint32_dec_eq(v___x_3721_, v___x_3722_);
if (v___x_3723_ == 0)
{
uint32_t v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = 48;
v___x_3725_ = lean_uint32_dec_le(v___x_3724_, v___x_3721_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Name_str___override(v___x_3719_, v_comp_3720_);
return v___x_3726_;
}
else
{
uint32_t v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = 57;
v___x_3728_ = lean_uint32_dec_le(v___x_3721_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_Name_str___override(v___x_3719_, v_comp_3720_);
return v___x_3729_;
}
else
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3720_);
lean_dec_ref(v_comp_3720_);
if (lean_obj_tag(v___x_3730_) == 1)
{
lean_object* v_val_3731_; lean_object* v___x_3732_; 
v_val_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_val_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3732_ = l_Lean_Name_num___override(v___x_3719_, v_val_3731_);
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec(v___x_3730_);
lean_dec(v___x_3719_);
v___x_3733_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3734_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3733_);
return v___x_3734_;
}
}
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = lean_string_drop(v_comp_3720_, v___x_3735_);
v___x_3737_ = lean_string_dropright(v___x_3736_, v___x_3735_);
v___x_3738_ = l_Lean_Name_str___override(v___x_3719_, v___x_3737_);
return v___x_3738_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3739_, lean_object* v_x_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3739_, v_x_3740_);
lean_dec(v_init_3739_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = lean_box(0);
v___x_3744_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3742_, v___x_3743_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_box(0);
return v___x_3745_;
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = lean_box(0);
v___x_3747_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3746_, v___x_3744_);
return v___x_3747_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3748_){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3749_ = lean_unsigned_to_nat(0u);
v___x_3750_ = lean_string_utf8_byte_size(v_s_3748_);
v___x_3751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3751_, 0, v_s_3748_);
lean_ctor_set(v___x_3751_, 1, v___x_3749_);
lean_ctor_set(v___x_3751_, 2, v___x_3750_);
v___x_3752_ = l_Substring_Raw_toName(v___x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3753_){
_start:
{
lean_object* v___x_3754_; uint32_t v___x_3755_; uint32_t v___x_3756_; uint8_t v___x_3757_; 
v___x_3754_ = lean_unsigned_to_nat(0u);
v___x_3755_ = lean_string_utf8_get(v_s_3753_, v___x_3754_);
v___x_3756_ = 96;
v___x_3757_ = lean_uint32_dec_eq(v___x_3755_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
lean_dec_ref(v_s_3753_);
v___x_3758_ = lean_box(0);
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3759_ = lean_string_utf8_byte_size(v_s_3753_);
v___x_3760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3760_, 0, v_s_3753_);
lean_ctor_set(v___x_3760_, 1, v___x_3754_);
lean_ctor_set(v___x_3760_, 2, v___x_3759_);
v___x_3761_ = lean_unsigned_to_nat(1u);
v___x_3762_ = lean_substring_drop(v___x_3760_, v___x_3761_);
v___x_3763_ = l_Substring_Raw_toName(v___x_3762_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_box(0);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
return v___x_3765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3766_){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3768_ = l_Lean_Syntax_isLit_x3f(v___x_3767_, v_stx_3766_);
if (lean_obj_tag(v___x_3768_) == 1)
{
lean_object* v_val_3769_; lean_object* v___x_3770_; 
v_val_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_val_3769_);
lean_dec_ref_known(v___x_3768_, 1);
v___x_3770_ = l_Lean_Syntax_decodeNameLit(v_val_3769_);
return v___x_3770_;
}
else
{
lean_object* v___x_3771_; 
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
return v___x_3771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3772_);
lean_dec(v_stx_3772_);
return v_res_3773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3774_){
_start:
{
if (lean_obj_tag(v_x_3774_) == 1)
{
lean_object* v_args_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_args_3775_ = lean_ctor_get(v_x_3774_, 2);
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = lean_array_get_size(v_args_3775_);
v___x_3778_ = lean_nat_dec_lt(v___x_3776_, v___x_3777_);
return v___x_3778_;
}
else
{
uint8_t v___x_3779_; 
v___x_3779_ = 0;
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3780_){
_start:
{
uint8_t v_res_3781_; lean_object* v_r_3782_; 
v_res_3781_ = l_Lean_Syntax_hasArgs(v_x_3780_);
lean_dec(v_x_3780_);
v_r_3782_ = lean_box(v_res_3781_);
return v_r_3782_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3783_){
_start:
{
if (lean_obj_tag(v_x_3783_) == 2)
{
uint8_t v___x_3784_; 
v___x_3784_ = 1;
return v___x_3784_;
}
else
{
uint8_t v___x_3785_; 
v___x_3785_ = 0;
return v___x_3785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3786_){
_start:
{
uint8_t v_res_3787_; lean_object* v_r_3788_; 
v_res_3787_ = l_Lean_Syntax_isAtom(v_x_3786_);
lean_dec(v_x_3786_);
v_r_3788_ = lean_box(v_res_3787_);
return v_r_3788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3789_, lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 2)
{
lean_object* v_val_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v_val_3791_ = lean_ctor_get(v_x_3790_, 1);
lean_inc_ref(v_val_3791_);
lean_dec_ref_known(v_x_3790_, 2);
v___x_3792_ = lean_string_trim(v_val_3791_);
v___x_3793_ = lean_string_trim(v_token_3789_);
v___x_3794_ = lean_string_dec_eq(v___x_3792_, v___x_3793_);
lean_dec_ref(v___x_3793_);
lean_dec_ref(v___x_3792_);
return v___x_3794_;
}
else
{
uint8_t v___x_3795_; 
lean_dec(v_x_3790_);
lean_dec_ref(v_token_3789_);
v___x_3795_ = 0;
return v___x_3795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3796_, lean_object* v_x_3797_){
_start:
{
uint8_t v_res_3798_; lean_object* v_r_3799_; 
v_res_3798_ = l_Lean_Syntax_isToken(v_token_3796_, v_x_3797_);
v_r_3799_ = lean_box(v_res_3798_);
return v_r_3799_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3800_){
_start:
{
switch(lean_obj_tag(v_stx_3800_))
{
case 1:
{
lean_object* v_kind_3801_; lean_object* v_args_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_kind_3801_ = lean_ctor_get(v_stx_3800_, 1);
v_args_3802_ = lean_ctor_get(v_stx_3800_, 2);
v___x_3803_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3804_ = lean_name_eq(v_kind_3801_, v___x_3803_);
if (v___x_3804_ == 0)
{
return v___x_3804_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = lean_array_get_size(v_args_3802_);
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = lean_nat_dec_eq(v___x_3805_, v___x_3806_);
return v___x_3807_;
}
}
case 0:
{
uint8_t v___x_3808_; 
v___x_3808_ = 1;
return v___x_3808_;
}
default: 
{
uint8_t v___x_3809_; 
v___x_3809_ = 0;
return v___x_3809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3810_){
_start:
{
uint8_t v_res_3811_; lean_object* v_r_3812_; 
v_res_3811_ = l_Lean_Syntax_isNone(v_stx_3810_);
lean_dec(v_stx_3810_);
v_r_3812_ = lean_box(v_res_3811_);
return v_r_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3813_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Syntax_getOptional_x3f(v_stx_3813_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_box(0);
return v___x_3815_;
}
else
{
lean_object* v_val_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3824_; 
v_val_3816_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3818_ = v___x_3814_;
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_val_3816_);
lean_dec(v___x_3814_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = l_Lean_Syntax_getId(v_val_3816_);
lean_dec(v_val_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3825_);
lean_dec(v_stx_3825_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3827_, lean_object* v_x_3828_){
_start:
{
if (lean_obj_tag(v_x_3828_) == 1)
{
lean_object* v_args_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v_args_3829_ = lean_ctor_get(v_x_3828_, 2);
lean_inc_ref(v_p_3827_);
lean_inc_ref(v_x_3828_);
v___x_3830_ = lean_apply_1(v_p_3827_, v_x_3828_);
v___x_3831_ = lean_unbox(v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; size_t v_sz_3834_; size_t v___x_3835_; lean_object* v___x_3836_; lean_object* v_fst_3837_; 
lean_inc_ref(v_args_3829_);
lean_dec_ref_known(v_x_3828_, 3);
v___x_3832_ = lean_box(0);
v___x_3833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3834_ = lean_array_size(v_args_3829_);
v___x_3835_ = ((size_t)0ULL);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3827_, v_args_3829_, v_sz_3834_, v___x_3835_, v___x_3833_);
lean_dec_ref(v_args_3829_);
v_fst_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_fst_3837_);
lean_dec_ref(v___x_3836_);
if (lean_obj_tag(v_fst_3837_) == 0)
{
return v___x_3832_;
}
else
{
lean_object* v_val_3838_; 
v_val_3838_ = lean_ctor_get(v_fst_3837_, 0);
lean_inc(v_val_3838_);
lean_dec_ref_known(v_fst_3837_, 1);
return v_val_3838_;
}
}
else
{
lean_object* v___x_3839_; 
lean_dec_ref(v_p_3827_);
v___x_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3839_, 0, v_x_3828_);
return v___x_3839_;
}
}
else
{
lean_object* v___x_3840_; uint8_t v___x_3841_; 
lean_inc(v_x_3828_);
v___x_3840_ = lean_apply_1(v_p_3827_, v_x_3828_);
v___x_3841_ = lean_unbox(v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; 
lean_dec(v_x_3828_);
v___x_3842_ = lean_box(0);
return v___x_3842_;
}
else
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_x_3828_);
return v___x_3843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3844_, lean_object* v_as_3845_, size_t v_sz_3846_, size_t v_i_3847_, lean_object* v_b_3848_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = lean_usize_dec_lt(v_i_3847_, v_sz_3846_);
if (v___x_3849_ == 0)
{
lean_dec_ref(v_p_3844_);
lean_inc_ref(v_b_3848_);
return v_b_3848_;
}
else
{
lean_object* v___x_3850_; lean_object* v_a_3851_; lean_object* v___x_3852_; 
v___x_3850_ = lean_box(0);
v_a_3851_ = lean_array_uget_borrowed(v_as_3845_, v_i_3847_);
lean_inc(v_a_3851_);
lean_inc_ref(v_p_3844_);
v___x_3852_ = l_Lean_Syntax_findAux(v_p_3844_, v_a_3851_);
if (lean_obj_tag(v___x_3852_) == 1)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec_ref(v_p_3844_);
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set(v___x_3854_, 1, v___x_3850_);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; size_t v___x_3856_; size_t v___x_3857_; 
lean_dec(v___x_3852_);
v___x_3855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3856_ = ((size_t)1ULL);
v___x_3857_ = lean_usize_add(v_i_3847_, v___x_3856_);
v_i_3847_ = v___x_3857_;
v_b_3848_ = v___x_3855_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3859_, lean_object* v_as_3860_, lean_object* v_sz_3861_, lean_object* v_i_3862_, lean_object* v_b_3863_){
_start:
{
size_t v_sz_boxed_3864_; size_t v_i_boxed_3865_; lean_object* v_res_3866_; 
v_sz_boxed_3864_ = lean_unbox_usize(v_sz_3861_);
lean_dec(v_sz_3861_);
v_i_boxed_3865_ = lean_unbox_usize(v_i_3862_);
lean_dec(v_i_3862_);
v_res_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3859_, v_as_3860_, v_sz_boxed_3864_, v_i_boxed_3865_, v_b_3863_);
lean_dec_ref(v_b_3863_);
lean_dec_ref(v_as_3860_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3867_, lean_object* v_p_3868_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Lean_Syntax_findAux(v_p_3868_, v_stx_3867_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3870_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Lean_Syntax_isNatLit_x3f(v_s_3870_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_unsigned_to_nat(0u);
return v___x_3872_;
}
else
{
lean_object* v_val_3873_; 
v_val_3873_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_val_3873_);
lean_dec_ref_known(v___x_3871_, 1);
return v_val_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_TSyntax_getNat(v_s_3874_);
lean_dec(v_s_3874_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3879_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3881_ = l_Lean_Syntax_isLit_x3f(v___x_3880_, v_stx_3879_);
if (lean_obj_tag(v___x_3881_) == 1)
{
lean_object* v_val_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_val_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3882_, v___x_3883_, v___x_3883_);
lean_dec(v_val_3882_);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; 
lean_dec(v___x_3881_);
v___x_3885_ = lean_box(0);
return v___x_3885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3886_);
lean_dec(v_stx_3886_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3888_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_unsigned_to_nat(0u);
return v___x_3890_;
}
else
{
lean_object* v_val_3891_; 
v_val_3891_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v___x_3889_, 1);
return v_val_3891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_TSyntax_getHexNumVal(v_s_3892_);
lean_dec(v_s_3892_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3894_, lean_object* v_p_3895_, lean_object* v_n_3896_){
_start:
{
uint8_t v___x_3897_; 
v___x_3897_ = lean_string_utf8_at_end(v_s_3894_, v_p_3895_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; uint32_t v___x_3899_; uint32_t v___x_3900_; uint8_t v___x_3901_; 
v___x_3898_ = lean_string_utf8_next(v_s_3894_, v_p_3895_);
v___x_3899_ = lean_string_utf8_get(v_s_3894_, v_p_3895_);
lean_dec(v_p_3895_);
v___x_3900_ = 95;
v___x_3901_ = lean_uint32_dec_eq(v___x_3899_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_add(v_n_3896_, v___x_3902_);
lean_dec(v_n_3896_);
v_p_3895_ = v___x_3898_;
v_n_3896_ = v___x_3903_;
goto _start;
}
else
{
v_p_3895_ = v___x_3898_;
goto _start;
}
}
else
{
lean_dec(v_p_3895_);
return v_n_3896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3906_, lean_object* v_p_3907_, lean_object* v_n_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3906_, v_p_3907_, v_n_3908_);
lean_dec_ref(v_s_3906_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3910_){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3912_ = l_Lean_Syntax_isLit_x3f(v___x_3911_, v_s_3910_);
if (lean_obj_tag(v___x_3912_) == 1)
{
lean_object* v_val_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v_val_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3913_, v___x_3914_, v___x_3914_);
lean_dec(v_val_3913_);
return v___x_3915_;
}
else
{
lean_object* v___x_3916_; 
lean_dec(v___x_3912_);
v___x_3916_ = lean_unsigned_to_nat(0u);
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_TSyntax_getHexNumSize(v_s_3917_);
lean_dec(v_s_3917_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Syntax_getId(v_s_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_TSyntax_getId(v_s_3921_);
lean_dec(v_s_3921_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v___x_3932_; 
v___x_3932_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3932_;
}
else
{
lean_object* v_val_3933_; 
v_val_3933_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v___x_3931_, 1);
return v_val_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_TSyntax_getScientific(v_s_3934_);
lean_dec(v_s_3934_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3936_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Syntax_isStrLit_x3f(v_s_3936_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v___x_3938_; 
v___x_3938_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3938_;
}
else
{
lean_object* v_val_3939_; 
v_val_3939_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v___x_3937_, 1);
return v_val_3939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_TSyntax_getString(v_s_3940_);
lean_dec(v_s_3940_);
return v_res_3941_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3942_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_Lean_Syntax_isCharLit_x3f(v_s_3942_);
if (lean_obj_tag(v___x_3943_) == 0)
{
uint32_t v___x_3944_; 
v___x_3944_ = 65;
return v___x_3944_;
}
else
{
lean_object* v_val_3945_; uint32_t v___x_3946_; 
v_val_3945_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3946_ = lean_unbox_uint32(v_val_3945_);
lean_dec(v_val_3945_);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3947_){
_start:
{
uint32_t v_res_3948_; lean_object* v_r_3949_; 
v_res_3948_ = l_Lean_TSyntax_getChar(v_s_3947_);
lean_dec(v_s_3947_);
v_r_3949_ = lean_box_uint32(v_res_3948_);
return v_r_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Syntax_isNameLit_x3f(v_s_3950_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_box(0);
return v___x_3952_;
}
else
{
lean_object* v_val_3953_; 
v_val_3953_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v___x_3951_, 1);
return v_val_3953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_TSyntax_getName(v_s_3954_);
lean_dec(v_s_3954_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3956_){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_3958_ = l_Lean_Syntax_getArg(v_s_3956_, v___x_3957_);
v___x_3959_ = l_Lean_Syntax_getId(v___x_3958_);
lean_dec(v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_TSyntax_getHygieneInfo(v_s_3960_);
lean_dec(v_s_3960_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3962_, lean_object* v_a_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3962_, v_a_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3965_, v_a_3966_);
lean_dec_ref(v_a_3966_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3968_){
_start:
{
lean_object* v___f_3969_; 
v___f_3969_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3969_, 0, v_sep_3968_);
return v___f_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3970_, lean_object* v_sep_3971_){
_start:
{
lean_object* v___f_3972_; 
v___f_3972_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3972_, 0, v_sep_3971_);
return v___f_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3973_, lean_object* v_sep_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3973_, v_sep_3974_);
lean_dec(v_k_3973_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3976_, lean_object* v_val_3977_, uint8_t v_canonical_3978_){
_start:
{
lean_object* v___x_3979_; lean_object* v_src_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v_imported_3983_; lean_object* v_ctx_3984_; lean_object* v_scopes_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4001_; 
v___x_3979_ = lean_unsigned_to_nat(0u);
v_src_3980_ = l_Lean_Syntax_getArg(v_s_3976_, v___x_3979_);
v___x_3981_ = l_Lean_Syntax_getId(v_src_3980_);
v___x_3982_ = l_Lean_extractMacroScopes(v___x_3981_);
v_imported_3983_ = lean_ctor_get(v___x_3982_, 1);
v_ctx_3984_ = lean_ctor_get(v___x_3982_, 2);
v_scopes_3985_ = lean_ctor_get(v___x_3982_, 3);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; 
v_unused_4002_ = lean_ctor_get(v___x_3982_, 0);
lean_dec(v_unused_4002_);
v___x_3987_ = v___x_3982_;
v_isShared_3988_ = v_isSharedCheck_4001_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_scopes_3985_);
lean_inc(v_ctx_3984_);
lean_inc(v_imported_3983_);
lean_dec(v___x_3982_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4001_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = l_Lean_Name_eraseMacroScopes(v_val_3977_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_imported_3983_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_ctx_3984_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v_scopes_3985_);
v___x_3991_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v_id_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_id_3992_ = l_Lean_MacroScopesView_review(v___x_3991_);
v___x_3993_ = l_Lean_SourceInfo_fromRef(v_src_3980_, v_canonical_3978_);
lean_dec(v_src_3980_);
v___x_3994_ = 1;
v___x_3995_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3977_, v___x_3994_);
v___x_3996_ = lean_string_utf8_byte_size(v___x_3995_);
v___x_3997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set(v___x_3997_, 1, v___x_3979_);
lean_ctor_set(v___x_3997_, 2, v___x_3996_);
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3993_);
lean_ctor_set(v___x_3999_, 1, v___x_3997_);
lean_ctor_set(v___x_3999_, 2, v_id_3992_);
lean_ctor_set(v___x_3999_, 3, v___x_3998_);
return v___x_3999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4003_, lean_object* v_val_4004_, lean_object* v_canonical_4005_){
_start:
{
uint8_t v_canonical_boxed_4006_; lean_object* v_res_4007_; 
v_canonical_boxed_4006_ = lean_unbox(v_canonical_4005_);
v_res_4007_ = l_Lean_HygieneInfo_mkIdent(v_s_4003_, v_val_4004_, v_canonical_boxed_4006_);
lean_dec(v_s_4003_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4008_, lean_object* v_inst_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = lean_apply_1(v_inst_4008_, v_a_4010_);
v___x_4012_ = lean_apply_1(v_inst_4009_, v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4013_, lean_object* v_inst_4014_){
_start:
{
lean_object* v___f_4015_; 
v___f_4015_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4015_, 0, v_inst_4013_);
lean_closure_set(v___f_4015_, 1, v_inst_4014_);
return v___f_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4016_, lean_object* v_k_4017_, lean_object* v_k_x27_4018_, lean_object* v_inst_4019_, lean_object* v_inst_4020_){
_start:
{
lean_object* v___f_4021_; 
v___f_4021_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4021_, 0, v_inst_4019_);
lean_closure_set(v___f_4021_, 1, v_inst_4020_);
return v___f_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4022_, lean_object* v_k_4023_, lean_object* v_k_x27_4024_, lean_object* v_inst_4025_, lean_object* v_inst_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4022_, v_k_4023_, v_k_x27_4024_, v_inst_4025_, v_inst_4026_);
lean_dec(v_k_x27_4024_);
lean_dec(v_k_4023_);
return v_res_4027_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4036_ = l_Lean_mkCIdent(v___x_4035_);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4042_ = l_Lean_mkCIdent(v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4043_){
_start:
{
if (v_x_4043_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4044_;
}
else
{
lean_object* v___x_4045_; 
v___x_4045_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4046_){
_start:
{
uint8_t v_x_85__boxed_4047_; lean_object* v_res_4048_; 
v_x_85__boxed_4047_ = lean_unbox(v_x_4046_);
v_res_4048_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4047_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4051_){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_box(2);
v___x_4053_ = l_Lean_Syntax_mkCharLit(v_val_4051_, v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4054_){
_start:
{
uint32_t v_val_boxed_4055_; lean_object* v_res_4056_; 
v_val_boxed_4055_ = lean_unbox_uint32(v_val_4054_);
lean_dec(v_val_4054_);
v_res_4056_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4055_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4059_){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_box(2);
v___x_4061_ = l_Lean_Syntax_mkStrLit(v_val_4059_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4064_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = l_Nat_reprFast(v_n_4064_);
v___x_4066_ = lean_box(2);
v___x_4067_ = l_Lean_Syntax_mkNumLit(v___x_4065_, v___x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4075_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4076_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4077_ = lean_substring_tostring(v_s_4075_);
v___x_4078_ = lean_box(2);
v___x_4079_ = l_Lean_Syntax_mkStrLit(v___x_4077_, v___x_4078_);
v___x_4080_ = lean_unsigned_to_nat(1u);
v___x_4081_ = lean_mk_empty_array_with_capacity(v___x_4080_);
v___x_4082_ = lean_array_push(v___x_4081_, v___x_4079_);
v___x_4083_ = l_Lean_Syntax_mkCApp(v___x_4076_, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4086_, lean_object* v_x_4087_){
_start:
{
switch(lean_obj_tag(v_x_4087_))
{
case 0:
{
uint8_t v___x_4088_; 
v___x_4088_ = l_List_isEmpty___redArg(v_acc_4086_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; 
v___x_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4089_, 0, v_acc_4086_);
return v___x_4089_;
}
else
{
lean_object* v___x_4090_; 
lean_dec(v_acc_4086_);
v___x_4090_ = lean_box(0);
return v___x_4090_;
}
}
case 1:
{
lean_object* v_pre_4091_; lean_object* v_str_4092_; lean_object* v_val_4094_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v_pre_4091_ = lean_ctor_get(v_x_4087_, 0);
lean_inc(v_pre_4091_);
v_str_4092_ = lean_ctor_get(v_x_4087_, 1);
lean_inc_ref(v_str_4092_);
lean_dec_ref_known(v_x_4087_, 2);
v___x_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = lean_string_utf8_byte_size(v_str_4092_);
v___x_4099_ = lean_nat_dec_lt(v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4100_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4101_ = lean_string_append(v___x_4100_, v_str_4092_);
lean_dec_ref(v_str_4092_);
v___x_4102_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4103_ = lean_string_append(v___x_4101_, v___x_4102_);
v_val_4094_ = v___x_4103_;
goto v___jp_4093_;
}
else
{
lean_object* v___f_4104_; uint8_t v___y_4106_; lean_object* v___f_4113_; uint32_t v___y_4120_; uint32_t v___y_4125_; uint8_t v_c_4139_; uint8_t v___x_4148_; uint8_t v___x_4149_; 
v___f_4104_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4113_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4139_ = lean_string_get_byte_fast(v_str_4092_, v___x_4097_);
v___x_4148_ = 97;
v___x_4149_ = lean_uint8_dec_le(v___x_4148_, v_c_4139_);
if (v___x_4149_ == 0)
{
goto v___jp_4143_;
}
else
{
uint8_t v___x_4150_; uint8_t v___x_4151_; 
v___x_4150_ = 122;
v___x_4151_ = lean_uint8_dec_le(v_c_4139_, v___x_4150_);
if (v___x_4151_ == 0)
{
goto v___jp_4143_;
}
else
{
goto v___jp_4136_;
}
}
v___jp_4105_:
{
if (v___y_4106_ == 0)
{
uint8_t v___x_4107_; 
lean_inc_ref(v_str_4092_);
v___x_4107_ = lean_string_any(v_str_4092_, v___f_4104_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4108_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4109_ = lean_string_append(v___x_4108_, v_str_4092_);
lean_dec_ref(v_str_4092_);
v___x_4110_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4111_ = lean_string_append(v___x_4109_, v___x_4110_);
v_val_4094_ = v___x_4111_;
goto v___jp_4093_;
}
else
{
lean_object* v___x_4112_; 
lean_dec_ref(v_str_4092_);
lean_dec(v_pre_4091_);
lean_dec(v_acc_4086_);
v___x_4112_ = lean_box(0);
return v___x_4112_;
}
}
else
{
v_val_4094_ = v_str_4092_;
goto v___jp_4093_;
}
}
v___jp_4114_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
lean_inc_ref(v_str_4092_);
v___x_4115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4115_, 0, v_str_4092_);
lean_ctor_set(v___x_4115_, 1, v___x_4097_);
lean_ctor_set(v___x_4115_, 2, v___x_4098_);
v___x_4116_ = lean_unsigned_to_nat(1u);
v___x_4117_ = lean_substring_drop(v___x_4115_, v___x_4116_);
v___x_4118_ = lean_substring_all(v___x_4117_, v___f_4113_);
v___y_4106_ = v___x_4118_;
goto v___jp_4105_;
}
v___jp_4119_:
{
uint32_t v___x_4121_; uint8_t v___x_4122_; 
v___x_4121_ = 95;
v___x_4122_ = lean_uint32_dec_eq(v___y_4120_, v___x_4121_);
if (v___x_4122_ == 0)
{
uint8_t v___x_4123_; 
v___x_4123_ = l_Lean_isLetterLike(v___y_4120_);
if (v___x_4123_ == 0)
{
v___y_4106_ = v___x_4123_;
goto v___jp_4105_;
}
else
{
goto v___jp_4114_;
}
}
else
{
goto v___jp_4114_;
}
}
v___jp_4124_:
{
uint32_t v___x_4126_; uint8_t v___x_4127_; 
v___x_4126_ = 97;
v___x_4127_ = lean_uint32_dec_le(v___x_4126_, v___y_4125_);
if (v___x_4127_ == 0)
{
v___y_4120_ = v___y_4125_;
goto v___jp_4119_;
}
else
{
uint32_t v___x_4128_; uint8_t v___x_4129_; 
v___x_4128_ = 122;
v___x_4129_ = lean_uint32_dec_le(v___y_4125_, v___x_4128_);
if (v___x_4129_ == 0)
{
v___y_4120_ = v___y_4125_;
goto v___jp_4119_;
}
else
{
goto v___jp_4114_;
}
}
}
v___jp_4130_:
{
uint32_t v___x_4131_; uint32_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4131_ = lean_string_utf8_get(v_str_4092_, v___x_4097_);
v___x_4132_ = 65;
v___x_4133_ = lean_uint32_dec_le(v___x_4132_, v___x_4131_);
if (v___x_4133_ == 0)
{
v___y_4125_ = v___x_4131_;
goto v___jp_4124_;
}
else
{
uint32_t v___x_4134_; uint8_t v___x_4135_; 
v___x_4134_ = 90;
v___x_4135_ = lean_uint32_dec_le(v___x_4131_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4125_ = v___x_4131_;
goto v___jp_4124_;
}
else
{
goto v___jp_4114_;
}
}
}
v___jp_4136_:
{
lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4137_ = lean_unsigned_to_nat(1u);
v___x_4138_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4092_, v___x_4137_);
if (v___x_4138_ == 0)
{
goto v___jp_4130_;
}
else
{
v___y_4106_ = v___x_4138_;
goto v___jp_4105_;
}
}
v___jp_4140_:
{
uint8_t v___x_4141_; uint8_t v___x_4142_; 
v___x_4141_ = 95;
v___x_4142_ = lean_uint8_dec_eq(v_c_4139_, v___x_4141_);
if (v___x_4142_ == 0)
{
goto v___jp_4130_;
}
else
{
goto v___jp_4136_;
}
}
v___jp_4143_:
{
uint8_t v___x_4144_; uint8_t v___x_4145_; 
v___x_4144_ = 65;
v___x_4145_ = lean_uint8_dec_le(v___x_4144_, v_c_4139_);
if (v___x_4145_ == 0)
{
goto v___jp_4140_;
}
else
{
uint8_t v___x_4146_; uint8_t v___x_4147_; 
v___x_4146_ = 90;
v___x_4147_ = lean_uint8_dec_le(v_c_4139_, v___x_4146_);
if (v___x_4147_ == 0)
{
goto v___jp_4140_;
}
else
{
goto v___jp_4136_;
}
}
}
}
v___jp_4093_:
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4095_, 0, v_val_4094_);
lean_ctor_set(v___x_4095_, 1, v_acc_4086_);
v_acc_4086_ = v___x_4095_;
v_x_4087_ = v_pre_4091_;
goto _start;
}
}
default: 
{
lean_object* v___x_4152_; 
lean_dec_ref_known(v_x_4087_, 2);
lean_dec(v_acc_4086_);
v___x_4152_ = lean_box(0);
return v___x_4152_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4160_ = l_Lean_mkCIdent(v___x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4171_){
_start:
{
switch(lean_obj_tag(v_x_4171_))
{
case 0:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4172_;
}
case 1:
{
lean_object* v_pre_4173_; lean_object* v_str_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_pre_4173_ = lean_ctor_get(v_x_4171_, 0);
lean_inc(v_pre_4173_);
v_str_4174_ = lean_ctor_get(v_x_4171_, 1);
lean_inc_ref(v_str_4174_);
lean_dec_ref_known(v_x_4171_, 2);
v___x_4175_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4176_ = l_Lean_quoteNameMk(v_pre_4173_);
v___x_4177_ = lean_box(2);
v___x_4178_ = l_Lean_Syntax_mkStrLit(v_str_4174_, v___x_4177_);
v___x_4179_ = lean_unsigned_to_nat(2u);
v___x_4180_ = lean_mk_empty_array_with_capacity(v___x_4179_);
v___x_4181_ = lean_array_push(v___x_4180_, v___x_4176_);
v___x_4182_ = lean_array_push(v___x_4181_, v___x_4178_);
v___x_4183_ = l_Lean_Syntax_mkCApp(v___x_4175_, v___x_4182_);
return v___x_4183_;
}
default: 
{
lean_object* v_pre_4184_; lean_object* v_i_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_pre_4184_ = lean_ctor_get(v_x_4171_, 0);
lean_inc(v_pre_4184_);
v_i_4185_ = lean_ctor_get(v_x_4171_, 1);
lean_inc(v_i_4185_);
lean_dec_ref_known(v_x_4171_, 2);
v___x_4186_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4187_ = l_Lean_quoteNameMk(v_pre_4184_);
v___x_4188_ = l_Nat_reprFast(v_i_4185_);
v___x_4189_ = lean_box(2);
v___x_4190_ = l_Lean_Syntax_mkNumLit(v___x_4188_, v___x_4189_);
v___x_4191_ = lean_unsigned_to_nat(2u);
v___x_4192_ = lean_mk_empty_array_with_capacity(v___x_4191_);
v___x_4193_ = lean_array_push(v___x_4192_, v___x_4187_);
v___x_4194_ = lean_array_push(v___x_4193_, v___x_4190_);
v___x_4195_ = l_Lean_Syntax_mkCApp(v___x_4186_, v___x_4194_);
return v___x_4195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4202_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = lean_box(0);
lean_inc(v_n_4202_);
v___x_4204_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4203_, v_n_4202_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_quoteNameMk(v_n_4202_);
return v___x_4205_;
}
else
{
lean_object* v_val_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_dec(v_n_4202_);
v_val_4206_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_val_4206_);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4207_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4208_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4209_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4210_ = lean_string_intercalate(v___x_4209_, v_val_4206_);
v___x_4211_ = lean_string_append(v___x_4208_, v___x_4210_);
lean_dec_ref(v___x_4210_);
v___x_4212_ = lean_box(2);
v___x_4213_ = l_Lean_Syntax_mkNameLit(v___x_4211_, v___x_4212_);
v___x_4214_ = lean_unsigned_to_nat(1u);
v___x_4215_ = lean_mk_empty_array_with_capacity(v___x_4214_);
v___x_4216_ = lean_array_push(v___x_4215_, v___x_4213_);
v___x_4217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4212_);
lean_ctor_set(v___x_4217_, 1, v___x_4207_);
lean_ctor_set(v___x_4217_, 2, v___x_4216_);
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4218_){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = lean_box(0);
lean_inc(v_n_4218_);
v___x_4220_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4219_, v_n_4218_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_quoteNameMk(v_n_4218_);
return v___x_4221_;
}
else
{
lean_object* v_val_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec(v_n_4218_);
v_val_4222_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_val_4222_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4223_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4224_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4225_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4226_ = lean_string_intercalate(v___x_4225_, v_val_4222_);
v___x_4227_ = lean_string_append(v___x_4224_, v___x_4226_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = lean_box(2);
v___x_4229_ = l_Lean_Syntax_mkNameLit(v___x_4227_, v___x_4228_);
v___x_4230_ = lean_unsigned_to_nat(1u);
v___x_4231_ = lean_mk_empty_array_with_capacity(v___x_4230_);
v___x_4232_ = lean_array_push(v___x_4231_, v___x_4229_);
v___x_4233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4228_);
lean_ctor_set(v___x_4233_, 1, v___x_4223_);
lean_ctor_set(v___x_4233_, 2, v___x_4232_);
return v___x_4233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4241_, lean_object* v_inst_4242_, lean_object* v_x_4243_){
_start:
{
lean_object* v_fst_4244_; lean_object* v_snd_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_fst_4244_ = lean_ctor_get(v_x_4243_, 0);
lean_inc(v_fst_4244_);
v_snd_4245_ = lean_ctor_get(v_x_4243_, 1);
lean_inc(v_snd_4245_);
lean_dec_ref(v_x_4243_);
v___x_4246_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4247_ = lean_apply_1(v_inst_4241_, v_fst_4244_);
v___x_4248_ = lean_apply_1(v_inst_4242_, v_snd_4245_);
v___x_4249_ = lean_unsigned_to_nat(2u);
v___x_4250_ = lean_mk_empty_array_with_capacity(v___x_4249_);
v___x_4251_ = lean_array_push(v___x_4250_, v___x_4247_);
v___x_4252_ = lean_array_push(v___x_4251_, v___x_4248_);
v___x_4253_ = l_Lean_Syntax_mkCApp(v___x_4246_, v___x_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4254_, lean_object* v_inst_4255_){
_start:
{
lean_object* v___f_4256_; 
v___f_4256_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4256_, 0, v_inst_4254_);
lean_closure_set(v___f_4256_, 1, v_inst_4255_);
return v___f_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4257_, lean_object* v_00_u03b2_4258_, lean_object* v_inst_4259_, lean_object* v_inst_4260_){
_start:
{
lean_object* v___f_4261_; 
v___f_4261_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4261_, 0, v_inst_4259_);
lean_closure_set(v___f_4261_, 1, v_inst_4260_);
return v___f_4261_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4267_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4268_ = l_Lean_mkCIdent(v___x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4273_, lean_object* v_x_4274_){
_start:
{
if (lean_obj_tag(v_x_4274_) == 0)
{
lean_object* v___x_4275_; 
lean_dec_ref(v_inst_4273_);
v___x_4275_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4275_;
}
else
{
lean_object* v_head_4276_; lean_object* v_tail_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v_head_4276_ = lean_ctor_get(v_x_4274_, 0);
lean_inc(v_head_4276_);
v_tail_4277_ = lean_ctor_get(v_x_4274_, 1);
lean_inc(v_tail_4277_);
lean_dec_ref_known(v_x_4274_, 2);
v___x_4278_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4273_);
v___x_4279_ = lean_apply_1(v_inst_4273_, v_head_4276_);
v___x_4280_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4273_, v_tail_4277_);
v___x_4281_ = lean_unsigned_to_nat(2u);
v___x_4282_ = lean_mk_empty_array_with_capacity(v___x_4281_);
v___x_4283_ = lean_array_push(v___x_4282_, v___x_4279_);
v___x_4284_ = lean_array_push(v___x_4283_, v___x_4280_);
v___x_4285_ = l_Lean_Syntax_mkCApp(v___x_4278_, v___x_4284_);
return v___x_4285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4286_, lean_object* v_inst_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4287_, v_x_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4290_, v_a_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4293_, lean_object* v_inst_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4294_, v_a_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4298_, 0, lean_box(0));
lean_closure_set(v___x_4298_, 1, v_inst_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4299_, lean_object* v_inst_4300_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4301_, 0, lean_box(0));
lean_closure_set(v___x_4301_, 1, v_inst_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4304_, lean_object* v_xs_4305_, lean_object* v_i_4306_, lean_object* v_args_4307_){
_start:
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = lean_array_get_size(v_xs_4305_);
v___x_4309_ = lean_nat_dec_lt(v_i_4306_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_dec(v_i_4306_);
lean_dec_ref(v_inst_4304_);
v___x_4310_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4311_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4312_ = l_Nat_reprFast(v___x_4308_);
v___x_4313_ = lean_string_append(v___x_4311_, v___x_4312_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = l_Lean_Name_mkStr2(v___x_4310_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_mkCApp(v___x_4314_, v_args_4307_);
return v___x_4315_;
}
else
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4316_ = lean_unsigned_to_nat(1u);
v___x_4317_ = lean_nat_add(v_i_4306_, v___x_4316_);
v___x_4318_ = lean_array_fget_borrowed(v_xs_4305_, v_i_4306_);
lean_dec(v_i_4306_);
lean_inc_ref(v_inst_4304_);
lean_inc(v___x_4318_);
v___x_4319_ = lean_apply_1(v_inst_4304_, v___x_4318_);
v___x_4320_ = lean_array_push(v_args_4307_, v___x_4319_);
v_i_4306_ = v___x_4317_;
v_args_4307_ = v___x_4320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4322_, lean_object* v_xs_4323_, lean_object* v_i_4324_, lean_object* v_args_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4322_, v_xs_4323_, v_i_4324_, v_args_4325_);
lean_dec_ref(v_xs_4323_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4327_, lean_object* v_inst_4328_, lean_object* v_xs_4329_, lean_object* v_i_4330_, lean_object* v_args_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4328_, v_xs_4329_, v_i_4330_, v_args_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4333_, lean_object* v_inst_4334_, lean_object* v_xs_4335_, lean_object* v_i_4336_, lean_object* v_args_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4333_, v_inst_4334_, v_xs_4335_, v_i_4336_, v_args_4337_);
lean_dec_ref(v_xs_4335_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4343_, lean_object* v_xs_4344_){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_4345_ = lean_array_get_size(v_xs_4344_);
v___x_4346_ = lean_unsigned_to_nat(8u);
v___x_4347_ = lean_nat_dec_le(v___x_4345_, v___x_4346_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4348_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4349_ = lean_array_to_list(v_xs_4344_);
v___x_4350_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4343_, v___x_4349_);
v___x_4351_ = lean_unsigned_to_nat(1u);
v___x_4352_ = lean_mk_empty_array_with_capacity(v___x_4351_);
v___x_4353_ = lean_array_push(v___x_4352_, v___x_4350_);
v___x_4354_ = l_Lean_Syntax_mkCApp(v___x_4348_, v___x_4353_);
return v___x_4354_;
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4357_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4343_, v_xs_4344_, v___x_4355_, v___x_4356_);
lean_dec_ref(v_xs_4344_);
return v___x_4357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4358_, lean_object* v_inst_4359_, lean_object* v_xs_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4359_, v_xs_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4362_, lean_object* v_xs_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4362_, v_xs_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4365_, lean_object* v_inst_4366_, lean_object* v_xs_4367_){
_start:
{
lean_object* v___x_4368_; 
v___x_4368_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4366_, v_xs_4367_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4370_, 0, lean_box(0));
lean_closure_set(v___x_4370_, 1, v_inst_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4371_, lean_object* v_inst_4372_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4373_, 0, lean_box(0));
lean_closure_set(v___x_4373_, 1, v_inst_4372_);
return v___x_4373_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4380_ = l_Lean_mkIdent(v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4385_, lean_object* v_x_4386_){
_start:
{
if (lean_obj_tag(v_x_4386_) == 0)
{
lean_object* v___x_4387_; 
lean_dec_ref(v_inst_4385_);
v___x_4387_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4387_;
}
else
{
lean_object* v_val_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v_val_4388_ = lean_ctor_get(v_x_4386_, 0);
lean_inc(v_val_4388_);
lean_dec_ref_known(v_x_4386_, 1);
v___x_4389_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4390_ = lean_apply_1(v_inst_4385_, v_val_4388_);
v___x_4391_ = lean_unsigned_to_nat(1u);
v___x_4392_ = lean_mk_empty_array_with_capacity(v___x_4391_);
v___x_4393_ = lean_array_push(v___x_4392_, v___x_4390_);
v___x_4394_ = l_Lean_Syntax_mkCApp(v___x_4389_, v___x_4393_);
return v___x_4394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4395_){
_start:
{
lean_object* v___f_4396_; 
v___f_4396_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4396_, 0, v_inst_4395_);
return v___f_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4397_, lean_object* v_inst_4398_){
_start:
{
lean_object* v___f_4399_; 
v___f_4399_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4399_, 0, v_inst_4398_);
return v___f_4399_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4400_, lean_object* v_k_4401_){
_start:
{
lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4402_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4403_ = lean_name_eq(v_k_4401_, v___x_4402_);
if (v___x_4403_ == 0)
{
uint8_t v___x_4404_; 
v___x_4404_ = 1;
return v___x_4404_;
}
else
{
return v___x_4400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4405_, lean_object* v_k_4406_){
_start:
{
uint8_t v___x_442__boxed_4407_; uint8_t v_res_4408_; lean_object* v_r_4409_; 
v___x_442__boxed_4407_ = lean_unbox(v___x_4405_);
v_res_4408_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4407_, v_k_4406_);
lean_dec(v_k_4406_);
v_r_4409_ = lean_box(v_res_4408_);
return v_r_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_methods_4414_; lean_object* v_quotContext_4415_; lean_object* v_currMacroScope_4416_; lean_object* v_currRecDepth_4417_; lean_object* v_maxRecDepth_4418_; lean_object* v_ref_4419_; uint8_t v___x_4420_; 
v_methods_4414_ = lean_ctor_get(v_a_4412_, 0);
v_quotContext_4415_ = lean_ctor_get(v_a_4412_, 1);
v_currMacroScope_4416_ = lean_ctor_get(v_a_4412_, 2);
v_currRecDepth_4417_ = lean_ctor_get(v_a_4412_, 3);
v_maxRecDepth_4418_ = lean_ctor_get(v_a_4412_, 4);
v_ref_4419_ = lean_ctor_get(v_a_4412_, 5);
v___x_4420_ = lean_nat_dec_eq(v_currRecDepth_4417_, v_maxRecDepth_4418_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4421_; lean_object* v___f_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4421_ = lean_box(v___x_4420_);
v___f_4422_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4422_, 0, v___x_4421_);
v___x_4423_ = lean_unsigned_to_nat(1u);
v___x_4424_ = lean_nat_add(v_currRecDepth_4417_, v___x_4423_);
lean_inc(v_ref_4419_);
lean_inc(v_maxRecDepth_4418_);
lean_inc(v_currMacroScope_4416_);
lean_inc(v_quotContext_4415_);
lean_inc(v_methods_4414_);
v___x_4425_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4425_, 0, v_methods_4414_);
lean_ctor_set(v___x_4425_, 1, v_quotContext_4415_);
lean_ctor_set(v___x_4425_, 2, v_currMacroScope_4416_);
lean_ctor_set(v___x_4425_, 3, v___x_4424_);
lean_ctor_set(v___x_4425_, 4, v_maxRecDepth_4418_);
lean_ctor_set(v___x_4425_, 5, v_ref_4419_);
lean_inc_ref(v___x_4425_);
v___x_4426_ = l_Lean_expandMacros(v_stx_4411_, v___f_4422_, v___x_4425_, v_a_4413_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4440_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_a_4428_ = lean_ctor_get(v___x_4426_, 1);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4430_ = v___x_4426_;
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; uint8_t v___x_4433_; 
v___x_4432_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4427_);
v___x_4433_ = l_Lean_Syntax_isOfKind(v_a_4427_, v___x_4432_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
lean_del_object(v___x_4430_);
v___x_4434_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4435_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4427_, v___x_4434_, v___x_4425_, v_a_4428_);
lean_dec_ref_known(v___x_4425_, 6);
lean_dec(v_a_4427_);
return v___x_4435_;
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
lean_dec_ref_known(v___x_4425_, 6);
v___x_4436_ = l_Lean_TSyntax_getNat(v_a_4427_);
lean_dec(v_a_4427_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4436_);
v___x_4438_ = v___x_4430_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v_a_4428_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec_ref_known(v___x_4425_, 6);
v_a_4441_ = lean_ctor_get(v___x_4426_, 0);
v_a_4442_ = lean_ctor_get(v___x_4426_, 1);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4426_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_inc(v_a_4441_);
lean_dec(v___x_4426_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4441_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4451_, 0, v_stx_4411_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
v___x_4452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
lean_ctor_set(v___x_4452_, 1, v_a_4413_);
return v___x_4452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Lean_evalPrec(v_stx_4453_, v_a_4454_, v_a_4455_);
lean_dec_ref(v_a_4454_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_methods_4461_; lean_object* v_quotContext_4462_; lean_object* v_currMacroScope_4463_; lean_object* v_currRecDepth_4464_; lean_object* v_maxRecDepth_4465_; lean_object* v_ref_4466_; uint8_t v___x_4467_; 
v_methods_4461_ = lean_ctor_get(v_a_4459_, 0);
v_quotContext_4462_ = lean_ctor_get(v_a_4459_, 1);
v_currMacroScope_4463_ = lean_ctor_get(v_a_4459_, 2);
v_currRecDepth_4464_ = lean_ctor_get(v_a_4459_, 3);
v_maxRecDepth_4465_ = lean_ctor_get(v_a_4459_, 4);
v_ref_4466_ = lean_ctor_get(v_a_4459_, 5);
v___x_4467_ = lean_nat_dec_eq(v_currRecDepth_4464_, v_maxRecDepth_4465_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___f_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4468_ = lean_box(v___x_4467_);
v___f_4469_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4469_, 0, v___x_4468_);
v___x_4470_ = lean_unsigned_to_nat(1u);
v___x_4471_ = lean_nat_add(v_currRecDepth_4464_, v___x_4470_);
lean_inc(v_ref_4466_);
lean_inc(v_maxRecDepth_4465_);
lean_inc(v_currMacroScope_4463_);
lean_inc(v_quotContext_4462_);
lean_inc(v_methods_4461_);
v___x_4472_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4472_, 0, v_methods_4461_);
lean_ctor_set(v___x_4472_, 1, v_quotContext_4462_);
lean_ctor_set(v___x_4472_, 2, v_currMacroScope_4463_);
lean_ctor_set(v___x_4472_, 3, v___x_4471_);
lean_ctor_set(v___x_4472_, 4, v_maxRecDepth_4465_);
lean_ctor_set(v___x_4472_, 5, v_ref_4466_);
lean_inc_ref(v___x_4472_);
v___x_4473_ = l_Lean_expandMacros(v_stx_4458_, v___f_4469_, v___x_4472_, v_a_4460_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4487_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
v_a_4475_ = lean_ctor_get(v___x_4473_, 1);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4477_ = v___x_4473_;
v_isShared_4478_ = v_isSharedCheck_4487_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_inc(v_a_4474_);
lean_dec(v___x_4473_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4487_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4474_);
v___x_4480_ = l_Lean_Syntax_isOfKind(v_a_4474_, v___x_4479_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_del_object(v___x_4477_);
v___x_4481_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4482_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4474_, v___x_4481_, v___x_4472_, v_a_4475_);
lean_dec_ref_known(v___x_4472_, 6);
lean_dec(v_a_4474_);
return v___x_4482_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4485_; 
lean_dec_ref_known(v___x_4472_, 6);
v___x_4483_ = l_Lean_TSyntax_getNat(v_a_4474_);
lean_dec(v_a_4474_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 0, v___x_4483_);
v___x_4485_ = v___x_4477_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v_a_4475_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec_ref_known(v___x_4472_, 6);
v_a_4488_ = lean_ctor_get(v___x_4473_, 0);
v_a_4489_ = lean_ctor_get(v___x_4473_, 1);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4473_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_inc(v_a_4488_);
lean_dec(v___x_4473_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4488_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4497_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4498_, 0, v_stx_4458_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
lean_ctor_set(v___x_4499_, 1, v_a_4460_);
return v___x_4499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_evalPrio(v_stx_4500_, v_a_4501_, v_a_4502_);
lean_dec_ref(v_a_4501_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
if (lean_obj_tag(v_x_4504_) == 0)
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = lean_unsigned_to_nat(1000u);
v___x_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
lean_ctor_set(v___x_4508_, 1, v_a_4506_);
return v___x_4508_;
}
else
{
lean_object* v_val_4509_; lean_object* v___x_4510_; 
v_val_4509_ = lean_ctor_get(v_x_4504_, 0);
lean_inc(v_val_4509_);
lean_dec_ref_known(v_x_4504_, 1);
v___x_4510_ = l_Lean_evalPrio(v_val_4509_, v_a_4505_, v_a_4506_);
return v___x_4510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_evalOptPrio(v_x_4511_, v_a_4512_, v_a_4513_);
lean_dec_ref(v_a_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4515_, lean_object* v_x1_4516_, lean_object* v_x2_4517_){
_start:
{
lean_object* v_fst_4518_; uint8_t v___x_4519_; 
v_fst_4518_ = lean_ctor_get(v_x1_4516_, 0);
v___x_4519_ = lean_unbox(v_fst_4518_);
if (v___x_4519_ == 0)
{
lean_object* v_snd_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_x2_4517_);
v_snd_4520_ = lean_ctor_get(v_x1_4516_, 1);
v_isSharedCheck_4528_ = !lean_is_exclusive(v_x1_4516_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v_x1_4516_, 0);
lean_dec(v_unused_4529_);
v___x_4522_ = v_x1_4516_;
v_isShared_4523_ = v_isSharedCheck_4528_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_snd_4520_);
lean_dec(v_x1_4516_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4528_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4524_ = lean_box(v___x_4515_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4524_);
v___x_4526_ = v___x_4522_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_snd_4520_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
else
{
lean_object* v_snd_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4540_; 
v_snd_4530_ = lean_ctor_get(v_x1_4516_, 1);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_x1_4516_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; 
v_unused_4541_ = lean_ctor_get(v_x1_4516_, 0);
lean_dec(v_unused_4541_);
v___x_4532_ = v_x1_4516_;
v_isShared_4533_ = v_isSharedCheck_4540_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_snd_4530_);
lean_dec(v_x1_4516_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4540_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4534_ = 0;
v___x_4535_ = lean_array_push(v_snd_4530_, v_x2_4517_);
v___x_4536_ = lean_box(v___x_4534_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 1, v___x_4535_);
lean_ctor_set(v___x_4532_, 0, v___x_4536_);
v___x_4538_ = v___x_4532_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v___x_4535_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4542_, lean_object* v_x1_4543_, lean_object* v_x2_4544_){
_start:
{
uint8_t v___x_87__boxed_4545_; lean_object* v_res_4546_; 
v___x_87__boxed_4545_ = lean_unbox(v___x_4542_);
v_res_4546_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4545_, v_x1_4543_, v_x2_4544_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4568_){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; uint8_t v___x_4573_; 
v___x_4569_ = lean_unsigned_to_nat(0u);
v___x_4570_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4571_ = lean_array_get_size(v_as_4568_);
v___x_4572_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4573_ = lean_nat_dec_lt(v___x_4569_, v___x_4571_);
if (v___x_4573_ == 0)
{
lean_dec_ref(v_as_4568_);
return v___x_4570_;
}
else
{
lean_object* v___x_4574_; lean_object* v___f_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; size_t v___x_4578_; size_t v___x_4579_; lean_object* v___x_4580_; lean_object* v_snd_4581_; 
v___x_4574_ = lean_box(v___x_4573_);
v___f_4575_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4575_, 0, v___x_4574_);
v___x_4576_ = lean_box(v___x_4573_);
v___x_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
lean_ctor_set(v___x_4577_, 1, v___x_4570_);
v___x_4578_ = ((size_t)0ULL);
v___x_4579_ = lean_usize_of_nat(v___x_4571_);
v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4572_, v___f_4575_, v_as_4568_, v___x_4578_, v___x_4579_, v___x_4577_);
v_snd_4581_ = lean_ctor_get(v___x_4580_, 1);
lean_inc(v_snd_4581_);
lean_dec(v___x_4580_);
return v_snd_4581_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4582_, lean_object* v_as_4583_){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; 
v___x_4584_ = lean_unsigned_to_nat(0u);
v___x_4585_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4586_ = lean_array_get_size(v_as_4583_);
v___x_4587_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4588_ = lean_nat_dec_lt(v___x_4584_, v___x_4586_);
if (v___x_4588_ == 0)
{
lean_dec_ref(v_as_4583_);
return v___x_4585_;
}
else
{
lean_object* v___x_4589_; lean_object* v___f_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; size_t v___x_4593_; size_t v___x_4594_; lean_object* v___x_4595_; lean_object* v_snd_4596_; 
v___x_4589_ = lean_box(v___x_4588_);
v___f_4590_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4590_, 0, v___x_4589_);
v___x_4591_ = lean_box(v___x_4588_);
v___x_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
lean_ctor_set(v___x_4592_, 1, v___x_4585_);
v___x_4593_ = ((size_t)0ULL);
v___x_4594_ = lean_usize_of_nat(v___x_4586_);
v___x_4595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4587_, v___f_4590_, v_as_4583_, v___x_4593_, v___x_4594_, v___x_4592_);
v_snd_4596_ = lean_ctor_get(v___x_4595_, 1);
lean_inc(v_snd_4596_);
lean_dec(v___x_4595_);
return v_snd_4596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4597_, lean_object* v_inst_4598_, lean_object* v_a_4599_, lean_object* v_p_4600_, lean_object* v_acc_4601_, lean_object* v_stx_4602_, uint8_t v_____do__lift_4603_){
_start:
{
if (v_____do__lift_4603_ == 0)
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
lean_dec(v_stx_4602_);
v___x_4612_ = lean_unsigned_to_nat(2u);
v___x_4613_ = lean_nat_add(v_i_4597_, v___x_4612_);
v___x_4614_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4598_, v_a_4599_, v_p_4600_, v___x_4613_, v_acc_4601_);
return v___x_4614_;
}
else
{
lean_object* v___x_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; 
v___x_4615_ = lean_array_get_size(v_acc_4601_);
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = lean_nat_dec_eq(v___x_4615_, v___x_4616_);
if (v___x_4617_ == 0)
{
uint8_t v___x_4618_; 
v___x_4618_ = lean_nat_dec_eq(v_i_4597_, v___x_4616_);
if (v___x_4618_ == 0)
{
goto v___jp_4604_;
}
else
{
if (v___x_4617_ == 0)
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4619_ = lean_unsigned_to_nat(2u);
v___x_4620_ = lean_nat_add(v_i_4597_, v___x_4619_);
v___x_4621_ = lean_array_push(v_acc_4601_, v_stx_4602_);
v___x_4622_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4598_, v_a_4599_, v_p_4600_, v___x_4620_, v___x_4621_);
return v___x_4622_;
}
else
{
goto v___jp_4604_;
}
}
}
else
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4623_ = lean_unsigned_to_nat(2u);
v___x_4624_ = lean_nat_add(v_i_4597_, v___x_4623_);
v___x_4625_ = lean_array_push(v_acc_4601_, v_stx_4602_);
v___x_4626_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4598_, v_a_4599_, v_p_4600_, v___x_4624_, v___x_4625_);
return v___x_4626_;
}
}
v___jp_4604_:
{
lean_object* v___x_4605_; lean_object* v_sepStx_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4605_ = lean_nat_pred(v_i_4597_);
v_sepStx_4606_ = lean_array_fget_borrowed(v_a_4599_, v___x_4605_);
lean_dec(v___x_4605_);
v___x_4607_ = lean_unsigned_to_nat(2u);
v___x_4608_ = lean_nat_add(v_i_4597_, v___x_4607_);
lean_inc(v_sepStx_4606_);
v___x_4609_ = lean_array_push(v_acc_4601_, v_sepStx_4606_);
v___x_4610_ = lean_array_push(v___x_4609_, v_stx_4602_);
v___x_4611_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4598_, v_a_4599_, v_p_4600_, v___x_4608_, v___x_4610_);
return v___x_4611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4627_, lean_object* v_inst_4628_, lean_object* v_a_4629_, lean_object* v_p_4630_, lean_object* v_acc_4631_, lean_object* v_stx_4632_, lean_object* v_____do__lift_4633_){
_start:
{
uint8_t v_____do__lift_208__boxed_4634_; lean_object* v_res_4635_; 
v_____do__lift_208__boxed_4634_ = lean_unbox(v_____do__lift_4633_);
v_res_4635_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4627_, v_inst_4628_, v_a_4629_, v_p_4630_, v_acc_4631_, v_stx_4632_, v_____do__lift_208__boxed_4634_);
lean_dec(v_i_4627_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4636_, lean_object* v_a_4637_, lean_object* v_p_4638_, lean_object* v_i_4639_, lean_object* v_acc_4640_){
_start:
{
lean_object* v_toApplicative_4641_; lean_object* v_toBind_4642_; lean_object* v_toPure_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_toApplicative_4641_ = lean_ctor_get(v_inst_4636_, 0);
v_toBind_4642_ = lean_ctor_get(v_inst_4636_, 1);
lean_inc(v_toBind_4642_);
v_toPure_4643_ = lean_ctor_get(v_toApplicative_4641_, 1);
v___x_4644_ = lean_array_get_size(v_a_4637_);
v___x_4645_ = lean_nat_dec_lt(v_i_4639_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; 
lean_inc(v_toPure_4643_);
lean_dec(v_toBind_4642_);
lean_dec(v_i_4639_);
lean_dec(v_p_4638_);
lean_dec_ref(v_a_4637_);
lean_dec_ref(v_inst_4636_);
v___x_4646_ = lean_apply_2(v_toPure_4643_, lean_box(0), v_acc_4640_);
return v___x_4646_;
}
else
{
lean_object* v_stx_4647_; lean_object* v___f_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v_stx_4647_ = lean_array_fget(v_a_4637_, v_i_4639_);
lean_inc(v_stx_4647_);
lean_inc(v_p_4638_);
v___f_4648_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4648_, 0, v_i_4639_);
lean_closure_set(v___f_4648_, 1, v_inst_4636_);
lean_closure_set(v___f_4648_, 2, v_a_4637_);
lean_closure_set(v___f_4648_, 3, v_p_4638_);
lean_closure_set(v___f_4648_, 4, v_acc_4640_);
lean_closure_set(v___f_4648_, 5, v_stx_4647_);
v___x_4649_ = lean_apply_1(v_p_4638_, v_stx_4647_);
v___x_4650_ = lean_apply_4(v_toBind_4642_, lean_box(0), lean_box(0), v___x_4649_, v___f_4648_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4651_, lean_object* v_inst_4652_, lean_object* v_a_4653_, lean_object* v_p_4654_, lean_object* v_i_4655_, lean_object* v_acc_4656_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4652_, v_a_4653_, v_p_4654_, v_i_4655_, v_acc_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4658_, lean_object* v_a_4659_, lean_object* v_p_4660_){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = lean_unsigned_to_nat(0u);
v___x_4662_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4663_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4658_, v_a_4659_, v_p_4660_, v___x_4661_, v___x_4662_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4664_, lean_object* v_inst_4665_, lean_object* v_a_4666_, lean_object* v_p_4667_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Array_filterSepElemsM___redArg(v_inst_4665_, v_a_4666_, v_p_4667_);
return v___x_4668_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4669_, lean_object* v_x_4670_){
_start:
{
lean_object* v___x_4671_; uint8_t v___x_4672_; 
v___x_4671_ = lean_apply_1(v_p_4669_, v_x_4670_);
v___x_4672_ = lean_unbox(v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4673_, lean_object* v_x_4674_){
_start:
{
uint8_t v_res_4675_; lean_object* v_r_4676_; 
v_res_4675_ = l_Array_filterSepElems___lam__0(v_p_4673_, v_x_4674_);
v_r_4676_ = lean_box(v_res_4675_);
return v_r_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4677_, lean_object* v_p_4678_, lean_object* v_i_4679_, lean_object* v_acc_4680_){
_start:
{
lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4681_ = lean_array_get_size(v_a_4677_);
v___x_4682_ = lean_nat_dec_lt(v_i_4679_, v___x_4681_);
if (v___x_4682_ == 0)
{
lean_dec(v_i_4679_);
lean_dec_ref(v_p_4678_);
return v_acc_4680_;
}
else
{
lean_object* v_stx_4683_; lean_object* v___x_4692_; uint8_t v___x_4693_; 
v_stx_4683_ = lean_array_fget_borrowed(v_a_4677_, v_i_4679_);
lean_inc_ref(v_p_4678_);
lean_inc(v_stx_4683_);
v___x_4692_ = lean_apply_1(v_p_4678_, v_stx_4683_);
v___x_4693_ = lean_unbox(v___x_4692_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = lean_unsigned_to_nat(2u);
v___x_4695_ = lean_nat_add(v_i_4679_, v___x_4694_);
lean_dec(v_i_4679_);
v_i_4679_ = v___x_4695_;
goto _start;
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; 
v___x_4697_ = lean_array_get_size(v_acc_4680_);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = lean_nat_dec_eq(v___x_4697_, v___x_4698_);
if (v___x_4699_ == 0)
{
uint8_t v___x_4700_; 
v___x_4700_ = lean_nat_dec_eq(v_i_4679_, v___x_4698_);
if (v___x_4700_ == 0)
{
goto v___jp_4684_;
}
else
{
if (v___x_4699_ == 0)
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4701_ = lean_unsigned_to_nat(2u);
v___x_4702_ = lean_nat_add(v_i_4679_, v___x_4701_);
lean_dec(v_i_4679_);
lean_inc(v_stx_4683_);
v___x_4703_ = lean_array_push(v_acc_4680_, v_stx_4683_);
v_i_4679_ = v___x_4702_;
v_acc_4680_ = v___x_4703_;
goto _start;
}
else
{
goto v___jp_4684_;
}
}
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4705_ = lean_unsigned_to_nat(2u);
v___x_4706_ = lean_nat_add(v_i_4679_, v___x_4705_);
lean_dec(v_i_4679_);
lean_inc(v_stx_4683_);
v___x_4707_ = lean_array_push(v_acc_4680_, v_stx_4683_);
v_i_4679_ = v___x_4706_;
v_acc_4680_ = v___x_4707_;
goto _start;
}
}
v___jp_4684_:
{
lean_object* v___x_4685_; lean_object* v_sepStx_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4685_ = lean_nat_pred(v_i_4679_);
v_sepStx_4686_ = lean_array_fget_borrowed(v_a_4677_, v___x_4685_);
lean_dec(v___x_4685_);
v___x_4687_ = lean_unsigned_to_nat(2u);
v___x_4688_ = lean_nat_add(v_i_4679_, v___x_4687_);
lean_dec(v_i_4679_);
lean_inc(v_sepStx_4686_);
v___x_4689_ = lean_array_push(v_acc_4680_, v_sepStx_4686_);
lean_inc(v_stx_4683_);
v___x_4690_ = lean_array_push(v___x_4689_, v_stx_4683_);
v_i_4679_ = v___x_4688_;
v_acc_4680_ = v___x_4690_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4709_, lean_object* v_p_4710_, lean_object* v_i_4711_, lean_object* v_acc_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4709_, v_p_4710_, v_i_4711_, v_acc_4712_);
lean_dec_ref(v_a_4709_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4714_, lean_object* v_p_4715_){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4718_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4714_, v_p_4715_, v___x_4716_, v___x_4717_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4719_, lean_object* v_p_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4719_, v_p_4720_);
lean_dec_ref(v_a_4719_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4722_, lean_object* v_p_4723_){
_start:
{
lean_object* v___f_4724_; lean_object* v___x_4725_; 
v___f_4724_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4724_, 0, v_p_4723_);
v___x_4725_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4722_, v___f_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4726_, lean_object* v_p_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Array_filterSepElems(v_a_4726_, v_p_4727_);
lean_dec_ref(v_a_4726_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4729_, lean_object* v_acc_4730_, lean_object* v_inst_4731_, lean_object* v_a_4732_, lean_object* v_f_4733_, lean_object* v_stx_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4729_, v_acc_4730_, v_inst_4731_, v_a_4732_, v_f_4733_, v_stx_4734_);
lean_dec(v_i_4729_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4736_, lean_object* v_a_4737_, lean_object* v_f_4738_, lean_object* v_i_4739_, lean_object* v_acc_4740_){
_start:
{
lean_object* v_toApplicative_4741_; lean_object* v_toBind_4742_; lean_object* v_toPure_4743_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v_toApplicative_4741_ = lean_ctor_get(v_inst_4736_, 0);
v_toBind_4742_ = lean_ctor_get(v_inst_4736_, 1);
v_toPure_4743_ = lean_ctor_get(v_toApplicative_4741_, 1);
v___x_4744_ = lean_array_get_size(v_a_4737_);
v___x_4745_ = lean_nat_dec_lt(v_i_4739_, v___x_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; 
lean_inc(v_toPure_4743_);
lean_dec(v_i_4739_);
lean_dec(v_f_4738_);
lean_dec_ref(v_a_4737_);
lean_dec_ref(v_inst_4736_);
v___x_4746_ = lean_apply_2(v_toPure_4743_, lean_box(0), v_acc_4740_);
return v___x_4746_;
}
else
{
lean_object* v_stx_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v_stx_4747_ = lean_array_fget_borrowed(v_a_4737_, v_i_4739_);
v___x_4748_ = lean_unsigned_to_nat(2u);
v___x_4749_ = lean_nat_mod(v_i_4739_, v___x_4748_);
v___x_4750_ = lean_unsigned_to_nat(0u);
v___x_4751_ = lean_nat_dec_eq(v___x_4749_, v___x_4750_);
lean_dec(v___x_4749_);
if (v___x_4751_ == 0)
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = lean_unsigned_to_nat(1u);
v___x_4753_ = lean_nat_add(v_i_4739_, v___x_4752_);
lean_dec(v_i_4739_);
lean_inc(v_stx_4747_);
v___x_4754_ = lean_array_push(v_acc_4740_, v_stx_4747_);
v_i_4739_ = v___x_4753_;
v_acc_4740_ = v___x_4754_;
goto _start;
}
else
{
lean_object* v___f_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
lean_inc(v_stx_4747_);
lean_inc(v_toBind_4742_);
lean_inc(v_f_4738_);
v___f_4756_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4756_, 0, v_i_4739_);
lean_closure_set(v___f_4756_, 1, v_acc_4740_);
lean_closure_set(v___f_4756_, 2, v_inst_4736_);
lean_closure_set(v___f_4756_, 3, v_a_4737_);
lean_closure_set(v___f_4756_, 4, v_f_4738_);
v___x_4757_ = lean_apply_1(v_f_4738_, v_stx_4747_);
v___x_4758_ = lean_apply_4(v_toBind_4742_, lean_box(0), lean_box(0), v___x_4757_, v___f_4756_);
return v___x_4758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4759_, lean_object* v_acc_4760_, lean_object* v_inst_4761_, lean_object* v_a_4762_, lean_object* v_f_4763_, lean_object* v_stx_4764_){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4765_ = lean_unsigned_to_nat(1u);
v___x_4766_ = lean_nat_add(v_i_4759_, v___x_4765_);
v___x_4767_ = lean_array_push(v_acc_4760_, v_stx_4764_);
v___x_4768_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4761_, v_a_4762_, v_f_4763_, v___x_4766_, v___x_4767_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4769_, lean_object* v_inst_4770_, lean_object* v_a_4771_, lean_object* v_f_4772_, lean_object* v_i_4773_, lean_object* v_acc_4774_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4770_, v_a_4771_, v_f_4772_, v_i_4773_, v_acc_4774_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4776_, lean_object* v_a_4777_, lean_object* v_f_4778_){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4779_ = lean_unsigned_to_nat(0u);
v___x_4780_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4781_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4776_, v_a_4777_, v_f_4778_, v___x_4779_, v___x_4780_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4782_, lean_object* v_inst_4783_, lean_object* v_a_4784_, lean_object* v_f_4785_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Array_mapSepElemsM___redArg(v_inst_4783_, v_a_4784_, v_f_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4787_, lean_object* v_x_4788_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = lean_apply_1(v_f_4787_, v_x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4790_, lean_object* v_f_4791_, lean_object* v_i_4792_, lean_object* v_acc_4793_){
_start:
{
lean_object* v___x_4794_; uint8_t v___x_4795_; 
v___x_4794_ = lean_array_get_size(v_a_4790_);
v___x_4795_ = lean_nat_dec_lt(v_i_4792_, v___x_4794_);
if (v___x_4795_ == 0)
{
lean_dec(v_i_4792_);
lean_dec_ref(v_f_4791_);
return v_acc_4793_;
}
else
{
lean_object* v_stx_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v_stx_4796_ = lean_array_fget_borrowed(v_a_4790_, v_i_4792_);
v___x_4797_ = lean_unsigned_to_nat(2u);
v___x_4798_ = lean_nat_mod(v_i_4792_, v___x_4797_);
v___x_4799_ = lean_unsigned_to_nat(0u);
v___x_4800_ = lean_nat_dec_eq(v___x_4798_, v___x_4799_);
lean_dec(v___x_4798_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = lean_unsigned_to_nat(1u);
v___x_4802_ = lean_nat_add(v_i_4792_, v___x_4801_);
lean_dec(v_i_4792_);
lean_inc(v_stx_4796_);
v___x_4803_ = lean_array_push(v_acc_4793_, v_stx_4796_);
v_i_4792_ = v___x_4802_;
v_acc_4793_ = v___x_4803_;
goto _start;
}
else
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
lean_inc_ref(v_f_4791_);
lean_inc(v_stx_4796_);
v___x_4805_ = lean_apply_1(v_f_4791_, v_stx_4796_);
v___x_4806_ = lean_unsigned_to_nat(1u);
v___x_4807_ = lean_nat_add(v_i_4792_, v___x_4806_);
lean_dec(v_i_4792_);
v___x_4808_ = lean_array_push(v_acc_4793_, v___x_4805_);
v_i_4792_ = v___x_4807_;
v_acc_4793_ = v___x_4808_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4810_, lean_object* v_f_4811_, lean_object* v_i_4812_, lean_object* v_acc_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4810_, v_f_4811_, v_i_4812_, v_acc_4813_);
lean_dec_ref(v_a_4810_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4815_, lean_object* v_f_4816_){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4817_ = lean_unsigned_to_nat(0u);
v___x_4818_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4819_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4815_, v_f_4816_, v___x_4817_, v___x_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4820_, lean_object* v_f_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4820_, v_f_4821_);
lean_dec_ref(v_a_4820_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4823_, lean_object* v_f_4824_){
_start:
{
lean_object* v___f_4825_; lean_object* v___x_4826_; 
v___f_4825_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4825_, 0, v_f_4824_);
v___x_4826_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4823_, v___f_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4827_, lean_object* v_f_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Array_mapSepElems(v_a_4827_, v_f_4828_);
lean_dec_ref(v_a_4827_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4830_, size_t v_i_4831_, size_t v_stop_4832_, lean_object* v_b_4833_){
_start:
{
lean_object* v___y_4835_; uint8_t v___x_4839_; 
v___x_4839_ = lean_usize_dec_eq(v_i_4831_, v_stop_4832_);
if (v___x_4839_ == 0)
{
lean_object* v_fst_4840_; uint8_t v___x_4841_; 
v_fst_4840_ = lean_ctor_get(v_b_4833_, 0);
v___x_4841_ = lean_unbox(v_fst_4840_);
if (v___x_4841_ == 0)
{
lean_object* v_snd_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4851_; 
v_snd_4842_ = lean_ctor_get(v_b_4833_, 1);
v_isSharedCheck_4851_ = !lean_is_exclusive(v_b_4833_);
if (v_isSharedCheck_4851_ == 0)
{
lean_object* v_unused_4852_; 
v_unused_4852_ = lean_ctor_get(v_b_4833_, 0);
lean_dec(v_unused_4852_);
v___x_4844_ = v_b_4833_;
v_isShared_4845_ = v_isSharedCheck_4851_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_snd_4842_);
lean_dec(v_b_4833_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4851_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4846_ = 1;
v___x_4847_ = lean_box(v___x_4846_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 0, v___x_4847_);
v___x_4849_ = v___x_4844_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_snd_4842_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
v___y_4835_ = v___x_4849_;
goto v___jp_4834_;
}
}
}
else
{
lean_object* v_snd_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4863_; 
v_snd_4853_ = lean_ctor_get(v_b_4833_, 1);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_b_4833_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; 
v_unused_4864_ = lean_ctor_get(v_b_4833_, 0);
lean_dec(v_unused_4864_);
v___x_4855_ = v_b_4833_;
v_isShared_4856_ = v_isSharedCheck_4863_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_snd_4853_);
lean_dec(v_b_4833_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4863_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4861_; 
v___x_4857_ = lean_array_uget_borrowed(v_as_4830_, v_i_4831_);
lean_inc(v___x_4857_);
v___x_4858_ = lean_array_push(v_snd_4853_, v___x_4857_);
v___x_4859_ = lean_box(v___x_4839_);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 1, v___x_4858_);
lean_ctor_set(v___x_4855_, 0, v___x_4859_);
v___x_4861_ = v___x_4855_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v___x_4858_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
v___y_4835_ = v___x_4861_;
goto v___jp_4834_;
}
}
}
}
else
{
return v_b_4833_;
}
v___jp_4834_:
{
size_t v___x_4836_; size_t v___x_4837_; 
v___x_4836_ = ((size_t)1ULL);
v___x_4837_ = lean_usize_add(v_i_4831_, v___x_4836_);
v_i_4831_ = v___x_4837_;
v_b_4833_ = v___y_4835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4865_, lean_object* v_i_4866_, lean_object* v_stop_4867_, lean_object* v_b_4868_){
_start:
{
size_t v_i_boxed_4869_; size_t v_stop_boxed_4870_; lean_object* v_res_4871_; 
v_i_boxed_4869_ = lean_unbox_usize(v_i_4866_);
lean_dec(v_i_4866_);
v_stop_boxed_4870_ = lean_unbox_usize(v_stop_4867_);
lean_dec(v_stop_4867_);
v_res_4871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4865_, v_i_boxed_4869_, v_stop_boxed_4870_, v_b_4868_);
lean_dec_ref(v_as_4865_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4872_){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; uint8_t v___x_4876_; 
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4875_ = lean_array_get_size(v_sa_4872_);
v___x_4876_ = lean_nat_dec_lt(v___x_4873_, v___x_4875_);
if (v___x_4876_ == 0)
{
return v___x_4874_;
}
else
{
lean_object* v___x_4877_; lean_object* v___x_4878_; size_t v___x_4879_; size_t v___x_4880_; lean_object* v___x_4881_; lean_object* v_snd_4882_; 
v___x_4877_ = lean_box(v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set(v___x_4878_, 1, v___x_4874_);
v___x_4879_ = ((size_t)0ULL);
v___x_4880_ = lean_usize_of_nat(v___x_4875_);
v___x_4881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4872_, v___x_4879_, v___x_4880_, v___x_4878_);
v_snd_4882_ = lean_ctor_get(v___x_4881_, 1);
lean_inc(v_snd_4882_);
lean_dec_ref(v___x_4881_);
return v_snd_4882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4883_);
lean_dec_ref(v_sa_4883_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4885_, lean_object* v_sa_4886_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4888_, lean_object* v_sa_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l_Lean_Syntax_SepArray_getElems(v_sep_4888_, v_sa_4889_);
lean_dec_ref(v_sa_4889_);
lean_dec_ref(v_sep_4888_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4891_){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4894_ = lean_array_get_size(v_sa_4891_);
v___x_4895_ = lean_nat_dec_lt(v___x_4892_, v___x_4894_);
if (v___x_4895_ == 0)
{
return v___x_4893_;
}
else
{
lean_object* v___x_4896_; lean_object* v___x_4897_; size_t v___x_4898_; size_t v___x_4899_; lean_object* v___x_4900_; lean_object* v_snd_4901_; 
v___x_4896_ = lean_box(v___x_4895_);
v___x_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
lean_ctor_set(v___x_4897_, 1, v___x_4893_);
v___x_4898_ = ((size_t)0ULL);
v___x_4899_ = lean_usize_of_nat(v___x_4894_);
v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4891_, v___x_4898_, v___x_4899_, v___x_4897_);
v_snd_4901_ = lean_ctor_get(v___x_4900_, 1);
lean_inc(v_snd_4901_);
lean_dec_ref(v___x_4900_);
return v_snd_4901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4902_);
lean_dec_ref(v_sa_4902_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4904_, lean_object* v_sep_4905_, lean_object* v_sa_4906_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4906_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4908_, lean_object* v_sep_4909_, lean_object* v_sa_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Syntax_TSepArray_getElems(v_k_4908_, v_sep_4909_, v_sa_4910_);
lean_dec_ref(v_sa_4910_);
lean_dec_ref(v_sep_4909_);
lean_dec(v_k_4908_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4912_, lean_object* v_sa_4913_, lean_object* v_e_4914_){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; 
v___x_4915_ = lean_array_get_size(v_sa_4913_);
v___x_4916_ = lean_unsigned_to_nat(0u);
v___x_4917_ = lean_nat_dec_eq(v___x_4915_, v___x_4916_);
if (v___x_4917_ == 0)
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4918_ = l_Lean_mkAtom(v_sep_4912_);
v___x_4919_ = lean_array_push(v_sa_4913_, v___x_4918_);
v___x_4920_ = lean_array_push(v___x_4919_, v_e_4914_);
return v___x_4920_;
}
else
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
lean_dec_ref(v_sa_4913_);
lean_dec_ref(v_sep_4912_);
v___x_4921_ = lean_unsigned_to_nat(1u);
v___x_4922_ = lean_mk_empty_array_with_capacity(v___x_4921_);
v___x_4923_ = lean_array_push(v___x_4922_, v_e_4914_);
return v___x_4923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4924_, lean_object* v_sep_4925_, lean_object* v_sa_4926_, lean_object* v_e_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4925_, v_sa_4926_, v_e_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4929_, lean_object* v_sep_4930_, lean_object* v_sa_4931_, lean_object* v_e_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Syntax_TSepArray_push(v_k_4929_, v_sep_4930_, v_sa_4931_, v_e_4932_);
lean_dec(v_k_4929_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4937_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4939_){
_start:
{
lean_object* v___x_4940_; 
v___x_4940_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4941_);
lean_dec_ref(v_sep_4941_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4946_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4947_; 
v___x_4947_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4948_, lean_object* v_k_4949_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4951_, lean_object* v_k_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4951_, v_k_4952_);
lean_dec_ref(v_k_4952_);
lean_dec(v_sep_4951_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4954_){
_start:
{
lean_inc_ref(v_v_4954_);
return v_v_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4955_);
lean_dec_ref(v_v_4955_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4959_; 
v___f_4959_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4962_, lean_object* v_sep_4963_){
_start:
{
lean_object* v___f_4964_; 
v___f_4964_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4965_, lean_object* v_sep_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4965_, v_sep_4966_);
lean_dec_ref(v_sep_4966_);
lean_dec(v_k_4965_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4968_, lean_object* v_sep_4969_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4970_, 0, v_k_4968_);
lean_closure_set(v___x_4970_, 1, v_sep_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4971_, lean_object* v_x_4972_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = lean_apply_1(v_inst_4971_, v_x_4972_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v___x_4976_; size_t v_sz_4977_; size_t v___x_4978_; lean_object* v___x_4979_; 
v___x_4976_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4977_ = lean_array_size(v_a_4975_);
v___x_4978_ = ((size_t)0ULL);
v___x_4979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4976_, v___f_4974_, v_sz_4977_, v___x_4978_, v_a_4975_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_4980_){
_start:
{
lean_object* v___f_4981_; lean_object* v___f_4982_; 
v___f_4981_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4981_, 0, v_inst_4980_);
v___f_4982_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4982_, 0, v___f_4981_);
return v___f_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_4983_, lean_object* v_k_x27_4984_, lean_object* v_inst_4985_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_4985_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_4987_, lean_object* v_k_x27_4988_, lean_object* v_inst_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_4987_, v_k_x27_4988_, v_inst_4989_);
lean_dec(v_k_x27_4988_);
lean_dec(v_k_4987_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_4991_){
_start:
{
lean_inc_ref(v_a_4991_);
return v_a_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_4992_);
lean_dec_ref(v_a_4992_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_4996_; 
v___f_4996_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_4999_){
_start:
{
lean_object* v___f_5000_; 
v___f_5000_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5001_);
lean_dec(v_k_5001_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5009_){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5010_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5011_ = lean_box(2);
v___x_5012_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5013_ = lean_unsigned_to_nat(2u);
v___x_5014_ = lean_mk_empty_array_with_capacity(v___x_5013_);
v___x_5015_ = lean_array_push(v___x_5014_, v_id_5009_);
v___x_5016_ = lean_array_push(v___x_5015_, v___x_5012_);
v___x_5017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5011_);
lean_ctor_set(v___x_5017_, 1, v___x_5010_);
lean_ctor_set(v___x_5017_, 2, v___x_5016_);
return v___x_5017_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = 123;
v___x_5022_ = lean_box_uint32(v___x_5021_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5023_, lean_object* v_i_5024_){
_start:
{
lean_object* v___x_5025_; 
v___x_5025_ = l_Lean_Syntax_decodeQuotedChar(v_s_5023_, v_i_5024_);
if (lean_obj_tag(v___x_5025_) == 0)
{
uint32_t v_c_5026_; uint32_t v___x_5027_; uint8_t v___x_5028_; 
v_c_5026_ = lean_string_utf8_get(v_s_5023_, v_i_5024_);
v___x_5027_ = 123;
v___x_5028_ = lean_uint32_dec_eq(v_c_5026_, v___x_5027_);
if (v___x_5028_ == 0)
{
return v___x_5025_;
}
else
{
lean_object* v_i_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v_i_5029_ = lean_string_utf8_next(v_s_5023_, v_i_5024_);
v___x_5030_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
lean_ctor_set(v___x_5031_, 1, v_i_5029_);
v___x_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5031_);
return v___x_5032_;
}
}
else
{
return v___x_5025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5033_, lean_object* v_i_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5033_, v_i_5034_);
lean_dec(v_i_5034_);
lean_dec_ref(v_s_5033_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5036_, lean_object* v_i_5037_, lean_object* v_acc_5038_){
_start:
{
uint32_t v_c_5039_; uint32_t v___x_5040_; uint8_t v___x_5041_; 
v_c_5039_ = lean_string_utf8_get(v_s_5036_, v_i_5037_);
v___x_5040_ = 34;
v___x_5041_ = lean_uint32_dec_eq(v_c_5039_, v___x_5040_);
if (v___x_5041_ == 0)
{
uint32_t v___x_5042_; uint8_t v___x_5043_; 
v___x_5042_ = 123;
v___x_5043_ = lean_uint32_dec_eq(v_c_5039_, v___x_5042_);
if (v___x_5043_ == 0)
{
lean_object* v_i_5044_; uint8_t v___x_5045_; 
v_i_5044_ = lean_string_utf8_next(v_s_5036_, v_i_5037_);
lean_dec(v_i_5037_);
v___x_5045_ = lean_string_utf8_at_end(v_s_5036_, v_i_5044_);
if (v___x_5045_ == 0)
{
uint32_t v___x_5046_; uint8_t v___x_5047_; 
v___x_5046_ = 92;
v___x_5047_ = lean_uint32_dec_eq(v_c_5039_, v___x_5046_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; 
v___x_5048_ = lean_string_push(v_acc_5038_, v_c_5039_);
v_i_5037_ = v_i_5044_;
v_acc_5038_ = v___x_5048_;
goto _start;
}
else
{
lean_object* v___x_5050_; 
v___x_5050_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5036_, v_i_5044_);
if (lean_obj_tag(v___x_5050_) == 1)
{
lean_object* v_val_5051_; lean_object* v_fst_5052_; lean_object* v_snd_5053_; uint32_t v___x_5054_; lean_object* v___x_5055_; 
lean_dec(v_i_5044_);
v_val_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_val_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v_fst_5052_ = lean_ctor_get(v_val_5051_, 0);
lean_inc(v_fst_5052_);
v_snd_5053_ = lean_ctor_get(v_val_5051_, 1);
lean_inc(v_snd_5053_);
lean_dec(v_val_5051_);
v___x_5054_ = lean_unbox_uint32(v_fst_5052_);
lean_dec(v_fst_5052_);
v___x_5055_ = lean_string_push(v_acc_5038_, v___x_5054_);
v_i_5037_ = v_snd_5053_;
v_acc_5038_ = v___x_5055_;
goto _start;
}
else
{
lean_object* v___x_5057_; 
lean_dec(v___x_5050_);
lean_inc_ref(v_s_5036_);
v___x_5057_ = l_Lean_Syntax_decodeStringGap(v_s_5036_, v_i_5044_);
lean_dec(v_i_5044_);
if (lean_obj_tag(v___x_5057_) == 1)
{
lean_object* v_val_5058_; 
v_val_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_val_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v_i_5037_ = v_val_5058_;
goto _start;
}
else
{
lean_object* v___x_5060_; 
lean_dec(v___x_5057_);
lean_dec_ref(v_acc_5038_);
lean_dec_ref(v_s_5036_);
v___x_5060_ = lean_box(0);
return v___x_5060_;
}
}
}
}
else
{
lean_object* v___x_5061_; 
lean_dec(v_i_5044_);
lean_dec_ref(v_acc_5038_);
lean_dec_ref(v_s_5036_);
v___x_5061_ = lean_box(0);
return v___x_5061_;
}
}
else
{
lean_object* v___x_5062_; 
lean_dec(v_i_5037_);
lean_dec_ref(v_s_5036_);
v___x_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5062_, 0, v_acc_5038_);
return v___x_5062_;
}
}
else
{
lean_object* v___x_5063_; 
lean_dec(v_i_5037_);
lean_dec_ref(v_s_5036_);
v___x_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5063_, 0, v_acc_5038_);
return v___x_5063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5064_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5065_ = lean_unsigned_to_nat(1u);
v___x_5066_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5067_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5064_, v___x_5065_, v___x_5066_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5071_){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5073_ = l_Lean_Syntax_isLit_x3f(v___x_5072_, v_stx_5071_);
if (lean_obj_tag(v___x_5073_) == 0)
{
return v___x_5073_;
}
else
{
lean_object* v_val_5074_; lean_object* v___x_5075_; 
v_val_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_val_5074_);
lean_dec_ref_known(v___x_5073_, 1);
v___x_5075_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5074_);
return v___x_5075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5076_);
lean_dec(v_stx_5076_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5078_){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; uint8_t v___x_5083_; 
v___x_5079_ = l_Lean_Syntax_getArgs(v_stx_5078_);
v___x_5080_ = lean_unsigned_to_nat(0u);
v___x_5081_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5082_ = lean_array_get_size(v___x_5079_);
v___x_5083_ = lean_nat_dec_lt(v___x_5080_, v___x_5082_);
if (v___x_5083_ == 0)
{
lean_dec_ref(v___x_5079_);
return v___x_5081_;
}
else
{
lean_object* v___x_5084_; lean_object* v___x_5085_; size_t v___x_5086_; size_t v___x_5087_; lean_object* v___x_5088_; lean_object* v_snd_5089_; 
v___x_5084_ = lean_box(v___x_5083_);
v___x_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5084_);
lean_ctor_set(v___x_5085_, 1, v___x_5081_);
v___x_5086_ = ((size_t)0ULL);
v___x_5087_ = lean_usize_of_nat(v___x_5082_);
v___x_5088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5079_, v___x_5086_, v___x_5087_, v___x_5085_);
lean_dec_ref(v___x_5079_);
v_snd_5089_ = lean_ctor_get(v___x_5088_, 1);
lean_inc(v_snd_5089_);
lean_dec_ref(v___x_5088_);
return v_snd_5089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lean_Syntax_getSepArgs(v_stx_5090_);
lean_dec(v_stx_5090_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5092_, lean_object* v_mkElem_5093_, lean_object* v_mkLit_5094_, lean_object* v_as_5095_, size_t v_sz_5096_, size_t v_i_5097_, lean_object* v_b_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v_a_5102_; lean_object* v_a_5103_; lean_object* v_elem_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; uint8_t v___x_5115_; 
v___x_5115_ = lean_usize_dec_lt(v_i_5097_, v_sz_5096_);
if (v___x_5115_ == 0)
{
lean_object* v___x_5116_; 
lean_dec_ref(v_mkLit_5094_);
lean_dec_ref(v_mkElem_5093_);
lean_dec_ref(v_mkAppend_5092_);
v___x_5116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5116_, 0, v_b_5098_);
lean_ctor_set(v___x_5116_, 1, v___y_5100_);
return v___x_5116_;
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5118_; 
v_a_5117_ = lean_array_uget_borrowed(v_as_5095_, v_i_5097_);
v___x_5118_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5117_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v_methods_5119_; lean_object* v_quotContext_5120_; lean_object* v_currMacroScope_5121_; lean_object* v_currRecDepth_5122_; lean_object* v_maxRecDepth_5123_; lean_object* v_ref_5124_; lean_object* v_ref_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v_methods_5119_ = lean_ctor_get(v___y_5099_, 0);
v_quotContext_5120_ = lean_ctor_get(v___y_5099_, 1);
v_currMacroScope_5121_ = lean_ctor_get(v___y_5099_, 2);
v_currRecDepth_5122_ = lean_ctor_get(v___y_5099_, 3);
v_maxRecDepth_5123_ = lean_ctor_get(v___y_5099_, 4);
v_ref_5124_ = lean_ctor_get(v___y_5099_, 5);
v_ref_5125_ = l_Lean_replaceRef(v_a_5117_, v_ref_5124_);
lean_inc(v_maxRecDepth_5123_);
lean_inc(v_currRecDepth_5122_);
lean_inc(v_currMacroScope_5121_);
lean_inc(v_quotContext_5120_);
lean_inc(v_methods_5119_);
v___x_5126_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5126_, 0, v_methods_5119_);
lean_ctor_set(v___x_5126_, 1, v_quotContext_5120_);
lean_ctor_set(v___x_5126_, 2, v_currMacroScope_5121_);
lean_ctor_set(v___x_5126_, 3, v_currRecDepth_5122_);
lean_ctor_set(v___x_5126_, 4, v_maxRecDepth_5123_);
lean_ctor_set(v___x_5126_, 5, v_ref_5125_);
lean_inc_ref(v_mkElem_5093_);
lean_inc(v_a_5117_);
v___x_5127_ = lean_apply_3(v_mkElem_5093_, v_a_5117_, v___x_5126_, v___y_5100_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v_a_5129_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
v_a_5129_ = lean_ctor_get(v___x_5127_, 1);
lean_inc(v_a_5129_);
lean_dec_ref_known(v___x_5127_, 2);
v_elem_5108_ = v_a_5128_;
v___y_5109_ = v___y_5099_;
v___y_5110_ = v_a_5129_;
goto v___jp_5107_;
}
else
{
lean_dec(v_b_5098_);
lean_dec_ref(v_mkLit_5094_);
lean_dec_ref(v_mkElem_5093_);
lean_dec_ref(v_mkAppend_5092_);
return v___x_5127_;
}
}
else
{
lean_object* v_val_5130_; uint8_t v___x_5131_; 
v_val_5130_ = lean_ctor_get(v___x_5118_, 0);
lean_inc_n(v_val_5130_, 2);
lean_dec_ref_known(v___x_5118_, 1);
v___x_5131_ = lean_string_isempty(v_val_5130_);
if (v___x_5131_ == 0)
{
lean_object* v_methods_5132_; lean_object* v_quotContext_5133_; lean_object* v_currMacroScope_5134_; lean_object* v_currRecDepth_5135_; lean_object* v_maxRecDepth_5136_; lean_object* v_ref_5137_; lean_object* v_ref_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v_methods_5132_ = lean_ctor_get(v___y_5099_, 0);
v_quotContext_5133_ = lean_ctor_get(v___y_5099_, 1);
v_currMacroScope_5134_ = lean_ctor_get(v___y_5099_, 2);
v_currRecDepth_5135_ = lean_ctor_get(v___y_5099_, 3);
v_maxRecDepth_5136_ = lean_ctor_get(v___y_5099_, 4);
v_ref_5137_ = lean_ctor_get(v___y_5099_, 5);
v_ref_5138_ = l_Lean_replaceRef(v_a_5117_, v_ref_5137_);
lean_inc(v_maxRecDepth_5136_);
lean_inc(v_currRecDepth_5135_);
lean_inc(v_currMacroScope_5134_);
lean_inc(v_quotContext_5133_);
lean_inc(v_methods_5132_);
v___x_5139_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5139_, 0, v_methods_5132_);
lean_ctor_set(v___x_5139_, 1, v_quotContext_5133_);
lean_ctor_set(v___x_5139_, 2, v_currMacroScope_5134_);
lean_ctor_set(v___x_5139_, 3, v_currRecDepth_5135_);
lean_ctor_set(v___x_5139_, 4, v_maxRecDepth_5136_);
lean_ctor_set(v___x_5139_, 5, v_ref_5138_);
lean_inc_ref(v_mkLit_5094_);
v___x_5140_ = lean_apply_3(v_mkLit_5094_, v_val_5130_, v___x_5139_, v___y_5100_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; lean_object* v_a_5142_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_a_5141_);
v_a_5142_ = lean_ctor_get(v___x_5140_, 1);
lean_inc(v_a_5142_);
lean_dec_ref_known(v___x_5140_, 2);
v_elem_5108_ = v_a_5141_;
v___y_5109_ = v___y_5099_;
v___y_5110_ = v_a_5142_;
goto v___jp_5107_;
}
else
{
lean_dec(v_b_5098_);
lean_dec_ref(v_mkLit_5094_);
lean_dec_ref(v_mkElem_5093_);
lean_dec_ref(v_mkAppend_5092_);
return v___x_5140_;
}
}
else
{
lean_dec(v_val_5130_);
v_a_5102_ = v_b_5098_;
v_a_5103_ = v___y_5100_;
goto v___jp_5101_;
}
}
}
v___jp_5101_:
{
size_t v___x_5104_; size_t v___x_5105_; 
v___x_5104_ = ((size_t)1ULL);
v___x_5105_ = lean_usize_add(v_i_5097_, v___x_5104_);
v_i_5097_ = v___x_5105_;
v_b_5098_ = v_a_5102_;
v___y_5100_ = v_a_5103_;
goto _start;
}
v___jp_5107_:
{
uint8_t v___x_5111_; 
v___x_5111_ = l_Lean_Syntax_isMissing(v_b_5098_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; 
lean_inc_ref(v_mkAppend_5092_);
lean_inc_ref(v___y_5109_);
v___x_5112_ = lean_apply_4(v_mkAppend_5092_, v_b_5098_, v_elem_5108_, v___y_5109_, v___y_5110_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v_a_5113_; lean_object* v_a_5114_; 
v_a_5113_ = lean_ctor_get(v___x_5112_, 0);
lean_inc(v_a_5113_);
v_a_5114_ = lean_ctor_get(v___x_5112_, 1);
lean_inc(v_a_5114_);
lean_dec_ref_known(v___x_5112_, 2);
v_a_5102_ = v_a_5113_;
v_a_5103_ = v_a_5114_;
goto v___jp_5101_;
}
else
{
lean_dec_ref(v_mkLit_5094_);
lean_dec_ref(v_mkElem_5093_);
lean_dec_ref(v_mkAppend_5092_);
return v___x_5112_;
}
}
else
{
lean_dec(v_b_5098_);
v_a_5102_ = v_elem_5108_;
v_a_5103_ = v___y_5110_;
goto v___jp_5101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5143_, lean_object* v_mkElem_5144_, lean_object* v_mkLit_5145_, lean_object* v_as_5146_, lean_object* v_sz_5147_, lean_object* v_i_5148_, lean_object* v_b_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
size_t v_sz_boxed_5152_; size_t v_i_boxed_5153_; lean_object* v_res_5154_; 
v_sz_boxed_5152_ = lean_unbox_usize(v_sz_5147_);
lean_dec(v_sz_5147_);
v_i_boxed_5153_ = lean_unbox_usize(v_i_5148_);
lean_dec(v_i_5148_);
v_res_5154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5143_, v_mkElem_5144_, v_mkLit_5145_, v_as_5146_, v_sz_boxed_5152_, v_i_boxed_5153_, v_b_5149_, v___y_5150_, v___y_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_as_5146_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5155_, lean_object* v_mkAppend_5156_, lean_object* v_mkElem_5157_, lean_object* v_mkLit_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v_result_5161_; size_t v_sz_5162_; size_t v___x_5163_; lean_object* v___x_5164_; 
v_result_5161_ = lean_box(0);
v_sz_5162_ = lean_array_size(v_chunks_5155_);
v___x_5163_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5158_);
v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5156_, v_mkElem_5157_, v_mkLit_5158_, v_chunks_5155_, v_sz_5162_, v___x_5163_, v_result_5161_, v_a_5159_, v_a_5160_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; lean_object* v_a_5166_; uint8_t v___x_5167_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
v_a_5166_ = lean_ctor_get(v___x_5164_, 1);
v___x_5167_ = l_Lean_Syntax_isMissing(v_a_5165_);
if (v___x_5167_ == 0)
{
lean_dec_ref(v_mkLit_5158_);
return v___x_5164_;
}
else
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5164_, 2);
v___x_5168_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5159_);
v___x_5169_ = lean_apply_3(v_mkLit_5158_, v___x_5168_, v_a_5159_, v_a_5166_);
return v___x_5169_;
}
}
else
{
lean_dec_ref(v_mkLit_5158_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5170_, lean_object* v_mkAppend_5171_, lean_object* v_mkElem_5172_, lean_object* v_mkLit_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5170_, v_mkAppend_5171_, v_mkElem_5172_, v_mkLit_5173_, v_a_5174_, v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec_ref(v_chunks_5170_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5181_, lean_object* v_b_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v_ref_5185_; uint8_t v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v_ref_5185_ = lean_ctor_get(v___y_5183_, 5);
v___x_5186_ = 0;
v___x_5187_ = l_Lean_SourceInfo_fromRef(v_ref_5185_, v___x_5186_);
v___x_5188_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5189_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5187_);
v___x_5190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5187_);
lean_ctor_set(v___x_5190_, 1, v___x_5189_);
v___x_5191_ = l_Lean_Syntax_node3(v___x_5187_, v___x_5188_, v_a_5181_, v___x_5190_, v_b_5182_);
v___x_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5191_);
lean_ctor_set(v___x_5192_, 1, v___y_5184_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5193_, lean_object* v_b_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5193_, v_b_5194_, v___y_5195_, v___y_5196_);
lean_dec_ref(v___y_5195_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5198_, lean_object* v_a_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_){
_start:
{
lean_object* v_ref_5202_; uint8_t v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
v_ref_5202_ = lean_ctor_get(v___y_5200_, 5);
v___x_5203_ = 0;
v___x_5204_ = l_Lean_SourceInfo_fromRef(v_ref_5202_, v___x_5203_);
v___x_5205_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5206_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5204_);
v___x_5207_ = l_Lean_Syntax_node1(v___x_5204_, v___x_5206_, v_a_5199_);
v___x_5208_ = l_Lean_Syntax_node2(v___x_5204_, v___x_5205_, v_ofInterpFn_5198_, v___x_5207_);
v___x_5209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5209_, 0, v___x_5208_);
lean_ctor_set(v___x_5209_, 1, v___y_5201_);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5210_, lean_object* v_a_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v_res_5214_; 
v_res_5214_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5210_, v_a_5211_, v___y_5212_, v___y_5213_);
lean_dec_ref(v___y_5212_);
return v_res_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5215_, lean_object* v_s_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_ref_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
v_ref_5219_ = lean_ctor_get(v___y_5217_, 5);
v___x_5220_ = 0;
v___x_5221_ = l_Lean_SourceInfo_fromRef(v_ref_5219_, v___x_5220_);
v___x_5222_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5223_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5224_ = lean_box(2);
v___x_5225_ = l_Lean_Syntax_mkStrLit(v_s_5216_, v___x_5224_);
lean_inc(v___x_5221_);
v___x_5226_ = l_Lean_Syntax_node1(v___x_5221_, v___x_5223_, v___x_5225_);
v___x_5227_ = l_Lean_Syntax_node2(v___x_5221_, v___x_5222_, v_ofLitFn_5215_, v___x_5226_);
v___x_5228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
lean_ctor_set(v___x_5228_, 1, v___y_5218_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5229_, lean_object* v_s_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5229_, v_s_5230_, v___y_5231_, v___y_5232_);
lean_dec_ref(v___y_5231_);
return v_res_5233_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5251_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5252_ = l_String_toRawSubstring_x27(v___x_5251_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5273_, lean_object* v_type_5274_, lean_object* v_ofInterpFn_5275_, lean_object* v_ofLitFn_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_){
_start:
{
lean_object* v___f_5279_; lean_object* v___f_5280_; lean_object* v___f_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___f_5279_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5280_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5280_, 0, v_ofInterpFn_5275_);
v___f_5281_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5281_, 0, v_ofLitFn_5276_);
v___x_5282_ = l_Lean_Syntax_getArgs(v_interpStr_5273_);
v___x_5283_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5282_, v___f_5279_, v___f_5280_, v___f_5281_, v_a_5277_, v_a_5278_);
lean_dec_ref(v___x_5282_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5316_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_a_5285_ = lean_ctor_get(v___x_5283_, 1);
v_isSharedCheck_5316_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5316_ == 0)
{
v___x_5287_ = v___x_5283_;
v_isShared_5288_ = v_isSharedCheck_5316_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5316_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v_quotContext_5289_; lean_object* v_currMacroScope_5290_; lean_object* v_ref_5291_; uint8_t v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5314_; 
v_quotContext_5289_ = lean_ctor_get(v_a_5277_, 1);
v_currMacroScope_5290_ = lean_ctor_get(v_a_5277_, 2);
v_ref_5291_ = lean_ctor_get(v_a_5277_, 5);
v___x_5292_ = 0;
v___x_5293_ = l_Lean_SourceInfo_fromRef(v_ref_5291_, v___x_5292_);
v___x_5294_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5295_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5296_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5293_, 7);
v___x_5297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5293_);
lean_ctor_set(v___x_5297_, 1, v___x_5296_);
v___x_5298_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5299_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5300_ = lean_box(0);
lean_inc(v_currMacroScope_5290_);
lean_inc(v_quotContext_5289_);
v___x_5301_ = l_Lean_addMacroScope(v_quotContext_5289_, v___x_5300_, v_currMacroScope_5290_);
v___x_5302_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5303_, 0, v___x_5293_);
lean_ctor_set(v___x_5303_, 1, v___x_5299_);
lean_ctor_set(v___x_5303_, 2, v___x_5301_);
lean_ctor_set(v___x_5303_, 3, v___x_5302_);
v___x_5304_ = l_Lean_Syntax_node1(v___x_5293_, v___x_5298_, v___x_5303_);
v___x_5305_ = l_Lean_Syntax_node2(v___x_5293_, v___x_5295_, v___x_5297_, v___x_5304_);
v___x_5306_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5293_);
lean_ctor_set(v___x_5307_, 1, v___x_5306_);
v___x_5308_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5309_ = l_Lean_Syntax_node1(v___x_5293_, v___x_5308_, v_type_5274_);
v___x_5310_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5293_);
lean_ctor_set(v___x_5311_, 1, v___x_5310_);
v___x_5312_ = l_Lean_Syntax_node5(v___x_5293_, v___x_5294_, v___x_5305_, v_a_5284_, v___x_5307_, v___x_5309_, v___x_5311_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5312_);
v___x_5314_ = v___x_5287_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5312_);
lean_ctor_set(v_reuseFailAlloc_5315_, 1, v_a_5285_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
}
else
{
lean_object* v_a_5317_; lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
lean_dec(v_type_5274_);
v_a_5317_ = lean_ctor_get(v___x_5283_, 0);
v_a_5318_ = lean_ctor_get(v___x_5283_, 1);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5283_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_inc(v_a_5317_);
lean_dec(v___x_5283_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5317_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5326_, lean_object* v_type_5327_, lean_object* v_ofInterpFn_5328_, lean_object* v_ofLitFn_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5326_, v_type_5327_, v_ofInterpFn_5328_, v_ofLitFn_5329_, v_a_5330_, v_a_5331_);
lean_dec_ref(v_a_5330_);
lean_dec(v_interpStr_5326_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5333_){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5334_ = lean_unsigned_to_nat(1u);
v___x_5335_ = l_Lean_Syntax_getArg(v_stx_5333_, v___x_5334_);
if (lean_obj_tag(v___x_5335_) == 1)
{
lean_object* v_kind_5336_; 
v_kind_5336_ = lean_ctor_get(v___x_5335_, 1);
lean_inc(v_kind_5336_);
if (lean_obj_tag(v_kind_5336_) == 1)
{
lean_object* v_pre_5337_; 
v_pre_5337_ = lean_ctor_get(v_kind_5336_, 0);
lean_inc(v_pre_5337_);
if (lean_obj_tag(v_pre_5337_) == 1)
{
lean_object* v_pre_5338_; 
v_pre_5338_ = lean_ctor_get(v_pre_5337_, 0);
lean_inc(v_pre_5338_);
if (lean_obj_tag(v_pre_5338_) == 1)
{
lean_object* v_pre_5339_; 
v_pre_5339_ = lean_ctor_get(v_pre_5338_, 0);
lean_inc(v_pre_5339_);
if (lean_obj_tag(v_pre_5339_) == 1)
{
lean_object* v_pre_5340_; 
v_pre_5340_ = lean_ctor_get(v_pre_5339_, 0);
if (lean_obj_tag(v_pre_5340_) == 0)
{
lean_object* v_args_5341_; lean_object* v_str_5342_; lean_object* v_str_5343_; lean_object* v_str_5344_; lean_object* v_str_5345_; lean_object* v___x_5346_; uint8_t v___x_5347_; 
v_args_5341_ = lean_ctor_get(v___x_5335_, 2);
lean_inc_ref(v_args_5341_);
lean_dec_ref_known(v___x_5335_, 3);
v_str_5342_ = lean_ctor_get(v_kind_5336_, 1);
lean_inc_ref(v_str_5342_);
lean_dec_ref_known(v_kind_5336_, 2);
v_str_5343_ = lean_ctor_get(v_pre_5337_, 1);
lean_inc_ref(v_str_5343_);
lean_dec_ref_known(v_pre_5337_, 2);
v_str_5344_ = lean_ctor_get(v_pre_5338_, 1);
lean_inc_ref(v_str_5344_);
lean_dec_ref_known(v_pre_5338_, 2);
v_str_5345_ = lean_ctor_get(v_pre_5339_, 1);
lean_inc_ref(v_str_5345_);
lean_dec_ref_known(v_pre_5339_, 2);
v___x_5346_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5347_ = lean_string_dec_eq(v_str_5345_, v___x_5346_);
lean_dec_ref(v_str_5345_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; 
lean_dec_ref(v_str_5344_);
lean_dec_ref(v_str_5343_);
lean_dec_ref(v_str_5342_);
lean_dec_ref(v_args_5341_);
v___x_5348_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5348_;
}
else
{
lean_object* v___x_5349_; uint8_t v___x_5350_; 
v___x_5349_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5350_ = lean_string_dec_eq(v_str_5344_, v___x_5349_);
lean_dec_ref(v_str_5344_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
lean_dec_ref(v_str_5343_);
lean_dec_ref(v_str_5342_);
lean_dec_ref(v_args_5341_);
v___x_5351_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5351_;
}
else
{
lean_object* v___x_5352_; uint8_t v___x_5353_; 
v___x_5352_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5353_ = lean_string_dec_eq(v_str_5343_, v___x_5352_);
lean_dec_ref(v_str_5343_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; 
lean_dec_ref(v_str_5342_);
lean_dec_ref(v_args_5341_);
v___x_5354_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5354_;
}
else
{
lean_object* v___x_5355_; uint8_t v___x_5356_; 
v___x_5355_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5356_ = lean_string_dec_eq(v_str_5342_, v___x_5355_);
lean_dec_ref(v_str_5342_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; 
lean_dec_ref(v_args_5341_);
v___x_5357_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5357_;
}
else
{
lean_object* v___x_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; 
v___x_5358_ = lean_array_get_size(v_args_5341_);
v___x_5359_ = lean_unsigned_to_nat(2u);
v___x_5360_ = lean_nat_dec_eq(v___x_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; 
lean_dec_ref(v_args_5341_);
v___x_5361_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5361_;
}
else
{
lean_object* v___x_5362_; lean_object* v___x_5363_; 
v___x_5362_ = lean_unsigned_to_nat(0u);
v___x_5363_ = lean_array_fget(v_args_5341_, v___x_5362_);
lean_dec_ref(v_args_5341_);
if (lean_obj_tag(v___x_5363_) == 2)
{
lean_object* v_val_5364_; 
v_val_5364_ = lean_ctor_get(v___x_5363_, 1);
lean_inc_ref(v_val_5364_);
lean_dec_ref_known(v___x_5363_, 2);
return v_val_5364_;
}
else
{
lean_object* v___x_5365_; 
lean_dec(v___x_5363_);
v___x_5365_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5365_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5366_; 
lean_dec_ref_known(v_pre_5339_, 2);
lean_dec_ref_known(v_pre_5338_, 2);
lean_dec_ref_known(v_pre_5337_, 2);
lean_dec_ref_known(v_kind_5336_, 2);
lean_dec_ref_known(v___x_5335_, 3);
v___x_5366_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5366_;
}
}
else
{
lean_object* v___x_5367_; 
lean_dec_ref_known(v_pre_5338_, 2);
lean_dec(v_pre_5339_);
lean_dec_ref_known(v_pre_5337_, 2);
lean_dec_ref_known(v_kind_5336_, 2);
lean_dec_ref_known(v___x_5335_, 3);
v___x_5367_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5367_;
}
}
else
{
lean_object* v___x_5368_; 
lean_dec_ref_known(v_pre_5337_, 2);
lean_dec(v_pre_5338_);
lean_dec_ref_known(v_kind_5336_, 2);
lean_dec_ref_known(v___x_5335_, 3);
v___x_5368_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5368_;
}
}
else
{
lean_object* v___x_5369_; 
lean_dec(v_pre_5337_);
lean_dec_ref_known(v_kind_5336_, 2);
lean_dec_ref_known(v___x_5335_, 3);
v___x_5369_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5369_;
}
}
else
{
lean_object* v___x_5370_; 
lean_dec_ref_known(v___x_5335_, 3);
lean_dec(v_kind_5336_);
v___x_5370_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5370_;
}
}
else
{
lean_object* v___x_5371_; 
lean_dec(v___x_5335_);
v___x_5371_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Lean_TSyntax_getDocString(v_stx_5372_);
lean_dec(v_stx_5372_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5392_, lean_object* v_prec_5393_){
_start:
{
lean_object* v___y_5395_; lean_object* v___y_5402_; lean_object* v___y_5409_; lean_object* v___y_5416_; lean_object* v___y_5423_; lean_object* v___y_5430_; 
switch(v_x_5392_)
{
case 0:
{
lean_object* v___x_5436_; uint8_t v___x_5437_; 
v___x_5436_ = lean_unsigned_to_nat(1024u);
v___x_5437_ = lean_nat_dec_le(v___x_5436_, v_prec_5393_);
if (v___x_5437_ == 0)
{
lean_object* v___x_5438_; 
v___x_5438_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5395_ = v___x_5438_;
goto v___jp_5394_;
}
else
{
lean_object* v___x_5439_; 
v___x_5439_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5395_ = v___x_5439_;
goto v___jp_5394_;
}
}
case 1:
{
lean_object* v___x_5440_; uint8_t v___x_5441_; 
v___x_5440_ = lean_unsigned_to_nat(1024u);
v___x_5441_ = lean_nat_dec_le(v___x_5440_, v_prec_5393_);
if (v___x_5441_ == 0)
{
lean_object* v___x_5442_; 
v___x_5442_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5402_ = v___x_5442_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5443_; 
v___x_5443_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5402_ = v___x_5443_;
goto v___jp_5401_;
}
}
case 2:
{
lean_object* v___x_5444_; uint8_t v___x_5445_; 
v___x_5444_ = lean_unsigned_to_nat(1024u);
v___x_5445_ = lean_nat_dec_le(v___x_5444_, v_prec_5393_);
if (v___x_5445_ == 0)
{
lean_object* v___x_5446_; 
v___x_5446_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5409_ = v___x_5446_;
goto v___jp_5408_;
}
else
{
lean_object* v___x_5447_; 
v___x_5447_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5409_ = v___x_5447_;
goto v___jp_5408_;
}
}
case 3:
{
lean_object* v___x_5448_; uint8_t v___x_5449_; 
v___x_5448_ = lean_unsigned_to_nat(1024u);
v___x_5449_ = lean_nat_dec_le(v___x_5448_, v_prec_5393_);
if (v___x_5449_ == 0)
{
lean_object* v___x_5450_; 
v___x_5450_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5416_ = v___x_5450_;
goto v___jp_5415_;
}
else
{
lean_object* v___x_5451_; 
v___x_5451_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5416_ = v___x_5451_;
goto v___jp_5415_;
}
}
case 4:
{
lean_object* v___x_5452_; uint8_t v___x_5453_; 
v___x_5452_ = lean_unsigned_to_nat(1024u);
v___x_5453_ = lean_nat_dec_le(v___x_5452_, v_prec_5393_);
if (v___x_5453_ == 0)
{
lean_object* v___x_5454_; 
v___x_5454_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5423_ = v___x_5454_;
goto v___jp_5422_;
}
else
{
lean_object* v___x_5455_; 
v___x_5455_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5423_ = v___x_5455_;
goto v___jp_5422_;
}
}
default: 
{
lean_object* v___x_5456_; uint8_t v___x_5457_; 
v___x_5456_ = lean_unsigned_to_nat(1024u);
v___x_5457_ = lean_nat_dec_le(v___x_5456_, v_prec_5393_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5430_ = v___x_5458_;
goto v___jp_5429_;
}
else
{
lean_object* v___x_5459_; 
v___x_5459_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5430_ = v___x_5459_;
goto v___jp_5429_;
}
}
}
v___jp_5394_:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; uint8_t v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5396_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5395_);
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
lean_inc(v___y_5402_);
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
lean_inc(v___y_5409_);
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
lean_inc(v___y_5416_);
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
lean_inc(v___y_5423_);
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
v___jp_5429_:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5431_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5430_);
v___x_5432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___y_5430_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = 0;
v___x_5434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5434_, 0, v___x_5432_);
lean_ctor_set_uint8(v___x_5434_, sizeof(void*)*1, v___x_5433_);
v___x_5435_ = l_Repr_addAppParen(v___x_5434_, v_prec_5393_);
return v___x_5435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5460_, lean_object* v_prec_5461_){
_start:
{
uint8_t v_x_329__boxed_5462_; lean_object* v_res_5463_; 
v_x_329__boxed_5462_ = lean_unbox(v_x_5460_);
v_res_5463_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5462_, v_prec_5461_);
lean_dec(v_prec_5461_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5475_, lean_object* v_prec_5476_){
_start:
{
lean_object* v___y_5478_; lean_object* v___y_5485_; lean_object* v___y_5492_; 
switch(v_x_5475_)
{
case 0:
{
lean_object* v___x_5498_; uint8_t v___x_5499_; 
v___x_5498_ = lean_unsigned_to_nat(1024u);
v___x_5499_ = lean_nat_dec_le(v___x_5498_, v_prec_5476_);
if (v___x_5499_ == 0)
{
lean_object* v___x_5500_; 
v___x_5500_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5478_ = v___x_5500_;
goto v___jp_5477_;
}
else
{
lean_object* v___x_5501_; 
v___x_5501_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5478_ = v___x_5501_;
goto v___jp_5477_;
}
}
case 1:
{
lean_object* v___x_5502_; uint8_t v___x_5503_; 
v___x_5502_ = lean_unsigned_to_nat(1024u);
v___x_5503_ = lean_nat_dec_le(v___x_5502_, v_prec_5476_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5485_ = v___x_5504_;
goto v___jp_5484_;
}
else
{
lean_object* v___x_5505_; 
v___x_5505_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5485_ = v___x_5505_;
goto v___jp_5484_;
}
}
default: 
{
lean_object* v___x_5506_; uint8_t v___x_5507_; 
v___x_5506_ = lean_unsigned_to_nat(1024u);
v___x_5507_ = lean_nat_dec_le(v___x_5506_, v_prec_5476_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5508_; 
v___x_5508_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5492_ = v___x_5508_;
goto v___jp_5491_;
}
else
{
lean_object* v___x_5509_; 
v___x_5509_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5492_ = v___x_5509_;
goto v___jp_5491_;
}
}
}
v___jp_5477_:
{
lean_object* v___x_5479_; lean_object* v___x_5480_; uint8_t v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5479_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5478_);
v___x_5480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5480_, 0, v___y_5478_);
lean_ctor_set(v___x_5480_, 1, v___x_5479_);
v___x_5481_ = 0;
v___x_5482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5482_, 0, v___x_5480_);
lean_ctor_set_uint8(v___x_5482_, sizeof(void*)*1, v___x_5481_);
v___x_5483_ = l_Repr_addAppParen(v___x_5482_, v_prec_5476_);
return v___x_5483_;
}
v___jp_5484_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; uint8_t v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5486_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5485_);
v___x_5487_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___y_5485_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v___x_5488_ = 0;
v___x_5489_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5489_, 0, v___x_5487_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*1, v___x_5488_);
v___x_5490_ = l_Repr_addAppParen(v___x_5489_, v_prec_5476_);
return v___x_5490_;
}
v___jp_5491_:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; uint8_t v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5493_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5492_);
v___x_5494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5494_, 0, v___y_5492_);
lean_ctor_set(v___x_5494_, 1, v___x_5493_);
v___x_5495_ = 0;
v___x_5496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5496_, 0, v___x_5494_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*1, v___x_5495_);
v___x_5497_ = l_Repr_addAppParen(v___x_5496_, v_prec_5476_);
return v___x_5497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5510_, lean_object* v_prec_5511_){
_start:
{
uint8_t v_x_167__boxed_5512_; lean_object* v_res_5513_; 
v_x_167__boxed_5512_ = lean_unbox(v_x_5510_);
v_res_5513_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5512_, v_prec_5511_);
lean_dec(v_prec_5511_);
return v_res_5513_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5525_ = lean_unsigned_to_nat(8u);
v___x_5526_ = lean_nat_to_int(v___x_5525_);
return v___x_5526_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_unsigned_to_nat(13u);
v___x_5537_ = lean_nat_to_int(v___x_5536_);
return v___x_5537_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5547_; lean_object* v___x_5548_; 
v___x_5547_ = lean_unsigned_to_nat(10u);
v___x_5548_ = lean_nat_to_int(v___x_5547_);
return v___x_5548_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5552_; lean_object* v___x_5553_; 
v___x_5552_ = lean_unsigned_to_nat(14u);
v___x_5553_ = lean_nat_to_int(v___x_5552_);
return v___x_5553_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5557_ = lean_unsigned_to_nat(19u);
v___x_5558_ = lean_nat_to_int(v___x_5557_);
return v___x_5558_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5562_ = lean_unsigned_to_nat(20u);
v___x_5563_ = lean_nat_to_int(v___x_5562_);
return v___x_5563_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
v___x_5570_ = lean_unsigned_to_nat(9u);
v___x_5571_ = lean_nat_to_int(v___x_5570_);
return v___x_5571_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = lean_unsigned_to_nat(12u);
v___x_5579_ = lean_nat_to_int(v___x_5578_);
return v___x_5579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5586_){
_start:
{
uint8_t v_zeta_5587_; uint8_t v_beta_5588_; uint8_t v_eta_5589_; uint8_t v_etaStruct_5590_; uint8_t v_iota_5591_; uint8_t v_proj_5592_; uint8_t v_decide_5593_; uint8_t v_autoUnfold_5594_; uint8_t v_failIfUnchanged_5595_; uint8_t v_unfoldPartialApp_5596_; uint8_t v_zetaDelta_5597_; uint8_t v_index_5598_; uint8_t v_zetaUnused_5599_; uint8_t v_zetaHave_5600_; uint8_t v_locals_5601_; uint8_t v_instances_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; uint8_t v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; 
v_zeta_5587_ = lean_ctor_get_uint8(v_x_5586_, 0);
v_beta_5588_ = lean_ctor_get_uint8(v_x_5586_, 1);
v_eta_5589_ = lean_ctor_get_uint8(v_x_5586_, 2);
v_etaStruct_5590_ = lean_ctor_get_uint8(v_x_5586_, 3);
v_iota_5591_ = lean_ctor_get_uint8(v_x_5586_, 4);
v_proj_5592_ = lean_ctor_get_uint8(v_x_5586_, 5);
v_decide_5593_ = lean_ctor_get_uint8(v_x_5586_, 6);
v_autoUnfold_5594_ = lean_ctor_get_uint8(v_x_5586_, 7);
v_failIfUnchanged_5595_ = lean_ctor_get_uint8(v_x_5586_, 8);
v_unfoldPartialApp_5596_ = lean_ctor_get_uint8(v_x_5586_, 9);
v_zetaDelta_5597_ = lean_ctor_get_uint8(v_x_5586_, 10);
v_index_5598_ = lean_ctor_get_uint8(v_x_5586_, 11);
v_zetaUnused_5599_ = lean_ctor_get_uint8(v_x_5586_, 12);
v_zetaHave_5600_ = lean_ctor_get_uint8(v_x_5586_, 13);
v_locals_5601_ = lean_ctor_get_uint8(v_x_5586_, 14);
v_instances_5602_ = lean_ctor_get_uint8(v_x_5586_, 15);
v___x_5603_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5604_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5605_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5606_ = lean_unsigned_to_nat(0u);
v___x_5607_ = l_Bool_repr___redArg(v_zeta_5587_);
v___x_5608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5608_, 0, v___x_5605_);
lean_ctor_set(v___x_5608_, 1, v___x_5607_);
v___x_5609_ = 0;
v___x_5610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5610_, 0, v___x_5608_);
lean_ctor_set_uint8(v___x_5610_, sizeof(void*)*1, v___x_5609_);
v___x_5611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5604_);
lean_ctor_set(v___x_5611_, 1, v___x_5610_);
v___x_5612_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5611_);
lean_ctor_set(v___x_5613_, 1, v___x_5612_);
v___x_5614_ = lean_box(1);
v___x_5615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5613_);
lean_ctor_set(v___x_5615_, 1, v___x_5614_);
v___x_5616_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5615_);
lean_ctor_set(v___x_5617_, 1, v___x_5616_);
v___x_5618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5617_);
lean_ctor_set(v___x_5618_, 1, v___x_5603_);
v___x_5619_ = l_Bool_repr___redArg(v_beta_5588_);
v___x_5620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5605_);
lean_ctor_set(v___x_5620_, 1, v___x_5619_);
v___x_5621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5621_, 0, v___x_5620_);
lean_ctor_set_uint8(v___x_5621_, sizeof(void*)*1, v___x_5609_);
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5618_);
lean_ctor_set(v___x_5622_, 1, v___x_5621_);
v___x_5623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set(v___x_5623_, 1, v___x_5612_);
v___x_5624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5623_);
lean_ctor_set(v___x_5624_, 1, v___x_5614_);
v___x_5625_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5624_);
lean_ctor_set(v___x_5626_, 1, v___x_5625_);
v___x_5627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set(v___x_5627_, 1, v___x_5603_);
v___x_5628_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5629_ = l_Bool_repr___redArg(v_eta_5589_);
v___x_5630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5628_);
lean_ctor_set(v___x_5630_, 1, v___x_5629_);
v___x_5631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5631_, 0, v___x_5630_);
lean_ctor_set_uint8(v___x_5631_, sizeof(void*)*1, v___x_5609_);
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5627_);
lean_ctor_set(v___x_5632_, 1, v___x_5631_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v___x_5612_);
v___x_5634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5633_);
lean_ctor_set(v___x_5634_, 1, v___x_5614_);
v___x_5635_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set(v___x_5637_, 1, v___x_5603_);
v___x_5638_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5639_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5590_, v___x_5606_);
v___x_5640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5638_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
lean_ctor_set_uint8(v___x_5641_, sizeof(void*)*1, v___x_5609_);
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5637_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
lean_ctor_set(v___x_5643_, 1, v___x_5612_);
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5643_);
lean_ctor_set(v___x_5644_, 1, v___x_5614_);
v___x_5645_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5644_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set(v___x_5647_, 1, v___x_5603_);
v___x_5648_ = l_Bool_repr___redArg(v_iota_5591_);
v___x_5649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5605_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
v___x_5650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*1, v___x_5609_);
v___x_5651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5647_);
lean_ctor_set(v___x_5651_, 1, v___x_5650_);
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5651_);
lean_ctor_set(v___x_5652_, 1, v___x_5612_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5614_);
v___x_5654_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5653_);
lean_ctor_set(v___x_5655_, 1, v___x_5654_);
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5655_);
lean_ctor_set(v___x_5656_, 1, v___x_5603_);
v___x_5657_ = l_Bool_repr___redArg(v_proj_5592_);
v___x_5658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5605_);
lean_ctor_set(v___x_5658_, 1, v___x_5657_);
v___x_5659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set_uint8(v___x_5659_, sizeof(void*)*1, v___x_5609_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5656_);
lean_ctor_set(v___x_5660_, 1, v___x_5659_);
v___x_5661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set(v___x_5661_, 1, v___x_5612_);
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
lean_ctor_set(v___x_5662_, 1, v___x_5614_);
v___x_5663_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5662_);
lean_ctor_set(v___x_5664_, 1, v___x_5663_);
v___x_5665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
lean_ctor_set(v___x_5665_, 1, v___x_5603_);
v___x_5666_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5667_ = l_Bool_repr___redArg(v_decide_5593_);
v___x_5668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5666_);
lean_ctor_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set_uint8(v___x_5669_, sizeof(void*)*1, v___x_5609_);
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5665_);
lean_ctor_set(v___x_5670_, 1, v___x_5669_);
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set(v___x_5671_, 1, v___x_5612_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
lean_ctor_set(v___x_5672_, 1, v___x_5614_);
v___x_5673_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5672_);
lean_ctor_set(v___x_5674_, 1, v___x_5673_);
v___x_5675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set(v___x_5675_, 1, v___x_5603_);
v___x_5676_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5677_ = l_Bool_repr___redArg(v_autoUnfold_5594_);
v___x_5678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5676_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*1, v___x_5609_);
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5675_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5680_);
lean_ctor_set(v___x_5681_, 1, v___x_5612_);
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set(v___x_5682_, 1, v___x_5614_);
v___x_5683_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5682_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set(v___x_5685_, 1, v___x_5603_);
v___x_5686_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5687_ = l_Bool_repr___redArg(v_failIfUnchanged_5595_);
v___x_5688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5686_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5689_, 0, v___x_5688_);
lean_ctor_set_uint8(v___x_5689_, sizeof(void*)*1, v___x_5609_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5685_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5612_);
v___x_5692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
lean_ctor_set(v___x_5692_, 1, v___x_5614_);
v___x_5693_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5603_);
v___x_5696_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5697_ = l_Bool_repr___redArg(v_unfoldPartialApp_5596_);
v___x_5698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set_uint8(v___x_5699_, sizeof(void*)*1, v___x_5609_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5695_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
lean_ctor_set(v___x_5701_, 1, v___x_5612_);
v___x_5702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5701_);
lean_ctor_set(v___x_5702_, 1, v___x_5614_);
v___x_5703_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5702_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v___x_5603_);
v___x_5706_ = l_Bool_repr___redArg(v_zetaDelta_5597_);
v___x_5707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5638_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v___x_5708_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5708_, 0, v___x_5707_);
lean_ctor_set_uint8(v___x_5708_, sizeof(void*)*1, v___x_5609_);
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5705_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set(v___x_5710_, 1, v___x_5612_);
v___x_5711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set(v___x_5711_, 1, v___x_5614_);
v___x_5712_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5713_);
lean_ctor_set(v___x_5714_, 1, v___x_5603_);
v___x_5715_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5716_ = l_Bool_repr___redArg(v_index_5598_);
v___x_5717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5715_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set_uint8(v___x_5718_, sizeof(void*)*1, v___x_5609_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5714_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
v___x_5720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5719_);
lean_ctor_set(v___x_5720_, 1, v___x_5612_);
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set(v___x_5721_, 1, v___x_5614_);
v___x_5722_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5721_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5723_);
lean_ctor_set(v___x_5724_, 1, v___x_5603_);
v___x_5725_ = l_Bool_repr___redArg(v_zetaUnused_5599_);
v___x_5726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5676_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5727_, 0, v___x_5726_);
lean_ctor_set_uint8(v___x_5727_, sizeof(void*)*1, v___x_5609_);
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5724_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set(v___x_5729_, 1, v___x_5612_);
v___x_5730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5729_);
lean_ctor_set(v___x_5730_, 1, v___x_5614_);
v___x_5731_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5730_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5732_);
lean_ctor_set(v___x_5733_, 1, v___x_5603_);
v___x_5734_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5735_ = l_Bool_repr___redArg(v_zetaHave_5600_);
v___x_5736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5734_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set_uint8(v___x_5737_, sizeof(void*)*1, v___x_5609_);
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5733_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
lean_ctor_set(v___x_5739_, 1, v___x_5612_);
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5739_);
lean_ctor_set(v___x_5740_, 1, v___x_5614_);
v___x_5741_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5740_);
lean_ctor_set(v___x_5742_, 1, v___x_5741_);
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5742_);
lean_ctor_set(v___x_5743_, 1, v___x_5603_);
v___x_5744_ = l_Bool_repr___redArg(v_locals_5601_);
v___x_5745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5666_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5746_, 0, v___x_5745_);
lean_ctor_set_uint8(v___x_5746_, sizeof(void*)*1, v___x_5609_);
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5743_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set(v___x_5748_, 1, v___x_5612_);
v___x_5749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5748_);
lean_ctor_set(v___x_5749_, 1, v___x_5614_);
v___x_5750_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5749_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
lean_ctor_set(v___x_5752_, 1, v___x_5603_);
v___x_5753_ = l_Bool_repr___redArg(v_instances_5602_);
v___x_5754_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5638_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v___x_5755_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5755_, 0, v___x_5754_);
lean_ctor_set_uint8(v___x_5755_, sizeof(void*)*1, v___x_5609_);
v___x_5756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5752_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v___x_5757_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5758_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5758_);
lean_ctor_set(v___x_5759_, 1, v___x_5756_);
v___x_5760_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5759_);
lean_ctor_set(v___x_5761_, 1, v___x_5760_);
v___x_5762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5757_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5763_, 0, v___x_5762_);
lean_ctor_set_uint8(v___x_5763_, sizeof(void*)*1, v___x_5609_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5764_);
lean_dec_ref(v_x_5764_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5766_, lean_object* v_prec_5767_){
_start:
{
lean_object* v___x_5768_; 
v___x_5768_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5766_);
return v___x_5768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5769_, lean_object* v_prec_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l_Lean_Meta_instReprConfig_repr(v_x_5769_, v_prec_5770_);
lean_dec(v_prec_5770_);
lean_dec_ref(v_x_5769_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5779_, lean_object* v_x_5780_){
_start:
{
if (lean_obj_tag(v_x_5779_) == 0)
{
lean_object* v___x_5781_; 
v___x_5781_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5781_;
}
else
{
lean_object* v_val_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5793_; 
v_val_5782_ = lean_ctor_get(v_x_5779_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v_x_5779_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5784_ = v_x_5779_;
v_isShared_5785_ = v_isSharedCheck_5793_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_val_5782_);
lean_dec(v_x_5779_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5793_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5789_; 
v___x_5786_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5787_ = l_Nat_reprFast(v_val_5782_);
if (v_isShared_5785_ == 0)
{
lean_ctor_set_tag(v___x_5784_, 3);
lean_ctor_set(v___x_5784_, 0, v___x_5787_);
v___x_5789_ = v___x_5784_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5790_; lean_object* v___x_5791_; 
v___x_5790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5790_, 0, v___x_5786_);
lean_ctor_set(v___x_5790_, 1, v___x_5789_);
v___x_5791_ = l_Repr_addAppParen(v___x_5790_, v_x_5780_);
return v___x_5791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5794_, lean_object* v_x_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5794_, v_x_5795_);
lean_dec(v_x_5795_);
return v_res_5796_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___x_5809_ = lean_unsigned_to_nat(21u);
v___x_5810_ = lean_nat_to_int(v___x_5809_);
return v___x_5810_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5817_ = lean_unsigned_to_nat(11u);
v___x_5818_ = lean_nat_to_int(v___x_5817_);
return v___x_5818_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5834_ = lean_unsigned_to_nat(23u);
v___x_5835_ = lean_nat_to_int(v___x_5834_);
return v___x_5835_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5839_; lean_object* v___x_5840_; 
v___x_5839_ = lean_unsigned_to_nat(16u);
v___x_5840_ = lean_nat_to_int(v___x_5839_);
return v___x_5840_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; 
v___x_5847_ = lean_unsigned_to_nat(15u);
v___x_5848_ = lean_nat_to_int(v___x_5847_);
return v___x_5848_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = lean_unsigned_to_nat(17u);
v___x_5856_ = lean_nat_to_int(v___x_5855_);
return v___x_5856_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5863_ = lean_unsigned_to_nat(18u);
v___x_5864_ = lean_nat_to_int(v___x_5863_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5865_){
_start:
{
lean_object* v_maxSteps_5866_; lean_object* v_maxDischargeDepth_5867_; uint8_t v_contextual_5868_; uint8_t v_memoize_5869_; uint8_t v_singlePass_5870_; uint8_t v_zeta_5871_; uint8_t v_beta_5872_; uint8_t v_eta_5873_; uint8_t v_etaStruct_5874_; uint8_t v_iota_5875_; uint8_t v_proj_5876_; uint8_t v_decide_5877_; uint8_t v_arith_5878_; uint8_t v_autoUnfold_5879_; uint8_t v_dsimp_5880_; uint8_t v_failIfUnchanged_5881_; uint8_t v_ground_5882_; uint8_t v_unfoldPartialApp_5883_; uint8_t v_zetaDelta_5884_; uint8_t v_index_5885_; uint8_t v_implicitDefEqProofs_5886_; uint8_t v_zetaUnused_5887_; uint8_t v_catchRuntime_5888_; uint8_t v_zetaHave_5889_; uint8_t v_letToHave_5890_; uint8_t v_congrConsts_5891_; uint8_t v_bitVecOfNat_5892_; uint8_t v_warnExponents_5893_; uint8_t v_suggestions_5894_; lean_object* v_maxSuggestions_5895_; uint8_t v_locals_5896_; uint8_t v_instances_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; uint8_t v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; 
v_maxSteps_5866_ = lean_ctor_get(v_x_5865_, 0);
lean_inc(v_maxSteps_5866_);
v_maxDischargeDepth_5867_ = lean_ctor_get(v_x_5865_, 1);
lean_inc(v_maxDischargeDepth_5867_);
v_contextual_5868_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3);
v_memoize_5869_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 1);
v_singlePass_5870_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 2);
v_zeta_5871_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 3);
v_beta_5872_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 4);
v_eta_5873_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 5);
v_etaStruct_5874_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 6);
v_iota_5875_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 7);
v_proj_5876_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 8);
v_decide_5877_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 9);
v_arith_5878_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 10);
v_autoUnfold_5879_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 11);
v_dsimp_5880_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5881_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 13);
v_ground_5882_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5883_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 15);
v_zetaDelta_5884_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 16);
v_index_5885_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5886_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 18);
v_zetaUnused_5887_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 19);
v_catchRuntime_5888_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 20);
v_zetaHave_5889_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 21);
v_letToHave_5890_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 22);
v_congrConsts_5891_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5892_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 24);
v_warnExponents_5893_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 25);
v_suggestions_5894_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 26);
v_maxSuggestions_5895_ = lean_ctor_get(v_x_5865_, 2);
lean_inc(v_maxSuggestions_5895_);
v_locals_5896_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 27);
v_instances_5897_ = lean_ctor_get_uint8(v_x_5865_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5865_);
v___x_5898_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5899_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5900_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5901_ = l_Nat_reprFast(v_maxSteps_5866_);
v___x_5902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5901_);
v___x_5903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5900_);
lean_ctor_set(v___x_5903_, 1, v___x_5902_);
v___x_5904_ = 0;
v___x_5905_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5905_, 0, v___x_5903_);
lean_ctor_set_uint8(v___x_5905_, sizeof(void*)*1, v___x_5904_);
v___x_5906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5899_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5906_);
lean_ctor_set(v___x_5908_, 1, v___x_5907_);
v___x_5909_ = lean_box(1);
v___x_5910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5908_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5912_);
lean_ctor_set(v___x_5913_, 1, v___x_5898_);
v___x_5914_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5915_ = l_Nat_reprFast(v_maxDischargeDepth_5867_);
v___x_5916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5915_);
v___x_5917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5914_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
v___x_5918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
lean_ctor_set_uint8(v___x_5918_, sizeof(void*)*1, v___x_5904_);
v___x_5919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5913_);
lean_ctor_set(v___x_5919_, 1, v___x_5918_);
v___x_5920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5919_);
lean_ctor_set(v___x_5920_, 1, v___x_5907_);
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5920_);
lean_ctor_set(v___x_5921_, 1, v___x_5909_);
v___x_5922_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5921_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5923_);
lean_ctor_set(v___x_5924_, 1, v___x_5898_);
v___x_5925_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5926_ = lean_unsigned_to_nat(0u);
v___x_5927_ = l_Bool_repr___redArg(v_contextual_5868_);
v___x_5928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5925_);
lean_ctor_set(v___x_5928_, 1, v___x_5927_);
v___x_5929_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*1, v___x_5904_);
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5924_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5907_);
v___x_5932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
lean_ctor_set(v___x_5932_, 1, v___x_5909_);
v___x_5933_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v___x_5898_);
v___x_5936_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5937_ = l_Bool_repr___redArg(v_memoize_5869_);
v___x_5938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5904_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5935_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5907_);
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5941_);
lean_ctor_set(v___x_5942_, 1, v___x_5909_);
v___x_5943_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set(v___x_5945_, 1, v___x_5898_);
v___x_5946_ = l_Bool_repr___redArg(v_singlePass_5870_);
v___x_5947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5925_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5948_, 0, v___x_5947_);
lean_ctor_set_uint8(v___x_5948_, sizeof(void*)*1, v___x_5904_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5945_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set(v___x_5950_, 1, v___x_5907_);
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set(v___x_5951_, 1, v___x_5909_);
v___x_5952_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5951_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set(v___x_5954_, 1, v___x_5898_);
v___x_5955_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5956_ = l_Bool_repr___redArg(v_zeta_5871_);
v___x_5957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5955_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set_uint8(v___x_5958_, sizeof(void*)*1, v___x_5904_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5954_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5959_);
lean_ctor_set(v___x_5960_, 1, v___x_5907_);
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set(v___x_5961_, 1, v___x_5909_);
v___x_5962_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5961_);
lean_ctor_set(v___x_5963_, 1, v___x_5962_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5963_);
lean_ctor_set(v___x_5964_, 1, v___x_5898_);
v___x_5965_ = l_Bool_repr___redArg(v_beta_5872_);
v___x_5966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5955_);
lean_ctor_set(v___x_5966_, 1, v___x_5965_);
v___x_5967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5967_, 0, v___x_5966_);
lean_ctor_set_uint8(v___x_5967_, sizeof(void*)*1, v___x_5904_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5964_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5907_);
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
lean_ctor_set(v___x_5970_, 1, v___x_5909_);
v___x_5971_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
v___x_5973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set(v___x_5973_, 1, v___x_5898_);
v___x_5974_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5975_ = l_Bool_repr___redArg(v_eta_5873_);
v___x_5976_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5974_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
lean_ctor_set_uint8(v___x_5977_, sizeof(void*)*1, v___x_5904_);
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5973_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5907_);
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set(v___x_5980_, 1, v___x_5909_);
v___x_5981_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5980_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
lean_ctor_set(v___x_5983_, 1, v___x_5898_);
v___x_5984_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5985_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5874_, v___x_5926_);
v___x_5986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5984_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
v___x_5987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set_uint8(v___x_5987_, sizeof(void*)*1, v___x_5904_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5983_);
lean_ctor_set(v___x_5988_, 1, v___x_5987_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5988_);
lean_ctor_set(v___x_5989_, 1, v___x_5907_);
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
lean_ctor_set(v___x_5990_, 1, v___x_5909_);
v___x_5991_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5990_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set(v___x_5993_, 1, v___x_5898_);
v___x_5994_ = l_Bool_repr___redArg(v_iota_5875_);
v___x_5995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5955_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set_uint8(v___x_5996_, sizeof(void*)*1, v___x_5904_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5993_);
lean_ctor_set(v___x_5997_, 1, v___x_5996_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5997_);
lean_ctor_set(v___x_5998_, 1, v___x_5907_);
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
lean_ctor_set(v___x_5999_, 1, v___x_5909_);
v___x_6000_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_5999_);
lean_ctor_set(v___x_6001_, 1, v___x_6000_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6001_);
lean_ctor_set(v___x_6002_, 1, v___x_5898_);
v___x_6003_ = l_Bool_repr___redArg(v_proj_5876_);
v___x_6004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_5955_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set_uint8(v___x_6005_, sizeof(void*)*1, v___x_5904_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6002_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5907_);
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6007_);
lean_ctor_set(v___x_6008_, 1, v___x_5909_);
v___x_6009_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6008_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set(v___x_6011_, 1, v___x_5898_);
v___x_6012_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6013_ = l_Bool_repr___redArg(v_decide_5877_);
v___x_6014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6012_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set_uint8(v___x_6015_, sizeof(void*)*1, v___x_5904_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6011_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5907_);
v___x_6018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6017_);
lean_ctor_set(v___x_6018_, 1, v___x_5909_);
v___x_6019_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6018_);
lean_ctor_set(v___x_6020_, 1, v___x_6019_);
v___x_6021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set(v___x_6021_, 1, v___x_5898_);
v___x_6022_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6023_ = l_Bool_repr___redArg(v_arith_5878_);
v___x_6024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6022_);
lean_ctor_set(v___x_6024_, 1, v___x_6023_);
v___x_6025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set_uint8(v___x_6025_, sizeof(void*)*1, v___x_5904_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6021_);
lean_ctor_set(v___x_6026_, 1, v___x_6025_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_5907_);
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set(v___x_6028_, 1, v___x_5909_);
v___x_6029_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6028_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set(v___x_6031_, 1, v___x_5898_);
v___x_6032_ = l_Bool_repr___redArg(v_autoUnfold_5879_);
v___x_6033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_5925_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*1, v___x_5904_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6031_);
lean_ctor_set(v___x_6035_, 1, v___x_6034_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
lean_ctor_set(v___x_6036_, 1, v___x_5907_);
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
lean_ctor_set(v___x_6037_, 1, v___x_5909_);
v___x_6038_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6037_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set(v___x_6040_, 1, v___x_5898_);
v___x_6041_ = l_Bool_repr___redArg(v_dsimp_5880_);
v___x_6042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6022_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
v___x_6043_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set_uint8(v___x_6043_, sizeof(void*)*1, v___x_5904_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6040_);
lean_ctor_set(v___x_6044_, 1, v___x_6043_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set(v___x_6045_, 1, v___x_5907_);
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6045_);
lean_ctor_set(v___x_6046_, 1, v___x_5909_);
v___x_6047_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6046_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6048_);
lean_ctor_set(v___x_6049_, 1, v___x_5898_);
v___x_6050_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6051_ = l_Bool_repr___redArg(v_failIfUnchanged_5881_);
v___x_6052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6050_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set_uint8(v___x_6053_, sizeof(void*)*1, v___x_5904_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6049_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_5907_);
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6055_);
lean_ctor_set(v___x_6056_, 1, v___x_5909_);
v___x_6057_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6056_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set(v___x_6059_, 1, v___x_5898_);
v___x_6060_ = l_Bool_repr___redArg(v_ground_5882_);
v___x_6061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6012_);
lean_ctor_set(v___x_6061_, 1, v___x_6060_);
v___x_6062_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
lean_ctor_set_uint8(v___x_6062_, sizeof(void*)*1, v___x_5904_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6059_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set(v___x_6064_, 1, v___x_5907_);
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
lean_ctor_set(v___x_6065_, 1, v___x_5909_);
v___x_6066_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6065_);
lean_ctor_set(v___x_6067_, 1, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
lean_ctor_set(v___x_6068_, 1, v___x_5898_);
v___x_6069_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6070_ = l_Bool_repr___redArg(v_unfoldPartialApp_5883_);
v___x_6071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6069_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set_uint8(v___x_6072_, sizeof(void*)*1, v___x_5904_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6068_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
lean_ctor_set(v___x_6074_, 1, v___x_5907_);
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set(v___x_6075_, 1, v___x_5909_);
v___x_6076_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6075_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
lean_ctor_set(v___x_6078_, 1, v___x_5898_);
v___x_6079_ = l_Bool_repr___redArg(v_zetaDelta_5884_);
v___x_6080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_5984_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6081_, 0, v___x_6080_);
lean_ctor_set_uint8(v___x_6081_, sizeof(void*)*1, v___x_5904_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6078_);
lean_ctor_set(v___x_6082_, 1, v___x_6081_);
v___x_6083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set(v___x_6083_, 1, v___x_5907_);
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6083_);
lean_ctor_set(v___x_6084_, 1, v___x_5909_);
v___x_6085_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6084_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
lean_ctor_set(v___x_6087_, 1, v___x_5898_);
v___x_6088_ = l_Bool_repr___redArg(v_index_5885_);
v___x_6089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6022_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
v___x_6090_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set_uint8(v___x_6090_, sizeof(void*)*1, v___x_5904_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6087_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
lean_ctor_set(v___x_6092_, 1, v___x_5907_);
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set(v___x_6093_, 1, v___x_5909_);
v___x_6094_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6093_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_5898_);
v___x_6097_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6098_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5886_);
v___x_6099_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6097_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set_uint8(v___x_6100_, sizeof(void*)*1, v___x_5904_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6096_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_5907_);
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
lean_ctor_set(v___x_6103_, 1, v___x_5909_);
v___x_6104_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6103_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
v___x_6106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set(v___x_6106_, 1, v___x_5898_);
v___x_6107_ = l_Bool_repr___redArg(v_zetaUnused_5887_);
v___x_6108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_5925_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set_uint8(v___x_6109_, sizeof(void*)*1, v___x_5904_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6106_);
lean_ctor_set(v___x_6110_, 1, v___x_6109_);
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set(v___x_6111_, 1, v___x_5907_);
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6111_);
lean_ctor_set(v___x_6112_, 1, v___x_5909_);
v___x_6113_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6112_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_5898_);
v___x_6116_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6117_ = l_Bool_repr___redArg(v_catchRuntime_5888_);
v___x_6118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6116_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set_uint8(v___x_6119_, sizeof(void*)*1, v___x_5904_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6115_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set(v___x_6121_, 1, v___x_5907_);
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set(v___x_6122_, 1, v___x_5909_);
v___x_6123_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6122_);
lean_ctor_set(v___x_6124_, 1, v___x_6123_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6124_);
lean_ctor_set(v___x_6125_, 1, v___x_5898_);
v___x_6126_ = l_Bool_repr___redArg(v_zetaHave_5889_);
v___x_6127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_5900_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
lean_ctor_set_uint8(v___x_6128_, sizeof(void*)*1, v___x_5904_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6125_);
lean_ctor_set(v___x_6129_, 1, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
lean_ctor_set(v___x_6130_, 1, v___x_5907_);
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6130_);
lean_ctor_set(v___x_6131_, 1, v___x_5909_);
v___x_6132_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6131_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
v___x_6134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
lean_ctor_set(v___x_6134_, 1, v___x_5898_);
v___x_6135_ = l_Bool_repr___redArg(v_letToHave_5890_);
v___x_6136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_5984_);
lean_ctor_set(v___x_6136_, 1, v___x_6135_);
v___x_6137_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set_uint8(v___x_6137_, sizeof(void*)*1, v___x_5904_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6134_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set(v___x_6139_, 1, v___x_5907_);
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
lean_ctor_set(v___x_6140_, 1, v___x_5909_);
v___x_6141_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6140_);
lean_ctor_set(v___x_6142_, 1, v___x_6141_);
v___x_6143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set(v___x_6143_, 1, v___x_5898_);
v___x_6144_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6145_ = l_Bool_repr___redArg(v_congrConsts_5891_);
v___x_6146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6144_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set_uint8(v___x_6147_, sizeof(void*)*1, v___x_5904_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6143_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
v___x_6149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set(v___x_6149_, 1, v___x_5907_);
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
lean_ctor_set(v___x_6150_, 1, v___x_5909_);
v___x_6151_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6150_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
v___x_6153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6152_);
lean_ctor_set(v___x_6153_, 1, v___x_5898_);
v___x_6154_ = l_Bool_repr___redArg(v_bitVecOfNat_5892_);
v___x_6155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6144_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
v___x_6156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
lean_ctor_set_uint8(v___x_6156_, sizeof(void*)*1, v___x_5904_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6153_);
lean_ctor_set(v___x_6157_, 1, v___x_6156_);
v___x_6158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
lean_ctor_set(v___x_6158_, 1, v___x_5907_);
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6158_);
lean_ctor_set(v___x_6159_, 1, v___x_5909_);
v___x_6160_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6159_);
lean_ctor_set(v___x_6161_, 1, v___x_6160_);
v___x_6162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6161_);
lean_ctor_set(v___x_6162_, 1, v___x_5898_);
v___x_6163_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6164_ = l_Bool_repr___redArg(v_warnExponents_5893_);
v___x_6165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6163_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set_uint8(v___x_6166_, sizeof(void*)*1, v___x_5904_);
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6162_);
lean_ctor_set(v___x_6167_, 1, v___x_6166_);
v___x_6168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6167_);
lean_ctor_set(v___x_6168_, 1, v___x_5907_);
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
lean_ctor_set(v___x_6169_, 1, v___x_5909_);
v___x_6170_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6169_);
lean_ctor_set(v___x_6171_, 1, v___x_6170_);
v___x_6172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6171_);
lean_ctor_set(v___x_6172_, 1, v___x_5898_);
v___x_6173_ = l_Bool_repr___redArg(v_suggestions_5894_);
v___x_6174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6144_);
lean_ctor_set(v___x_6174_, 1, v___x_6173_);
v___x_6175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
lean_ctor_set_uint8(v___x_6175_, sizeof(void*)*1, v___x_5904_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6172_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set(v___x_6177_, 1, v___x_5907_);
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6177_);
lean_ctor_set(v___x_6178_, 1, v___x_5909_);
v___x_6179_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6178_);
lean_ctor_set(v___x_6180_, 1, v___x_6179_);
v___x_6181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
lean_ctor_set(v___x_6181_, 1, v___x_5898_);
v___x_6182_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6183_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5895_, v___x_5926_);
v___x_6184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6182_);
lean_ctor_set(v___x_6184_, 1, v___x_6183_);
v___x_6185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set_uint8(v___x_6185_, sizeof(void*)*1, v___x_5904_);
v___x_6186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6181_);
lean_ctor_set(v___x_6186_, 1, v___x_6185_);
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___x_5907_);
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
lean_ctor_set(v___x_6188_, 1, v___x_5909_);
v___x_6189_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6188_);
lean_ctor_set(v___x_6190_, 1, v___x_6189_);
v___x_6191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6190_);
lean_ctor_set(v___x_6191_, 1, v___x_5898_);
v___x_6192_ = l_Bool_repr___redArg(v_locals_5896_);
v___x_6193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6012_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6194_, 0, v___x_6193_);
lean_ctor_set_uint8(v___x_6194_, sizeof(void*)*1, v___x_5904_);
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6191_);
lean_ctor_set(v___x_6195_, 1, v___x_6194_);
v___x_6196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
lean_ctor_set(v___x_6196_, 1, v___x_5907_);
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6196_);
lean_ctor_set(v___x_6197_, 1, v___x_5909_);
v___x_6198_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6197_);
lean_ctor_set(v___x_6199_, 1, v___x_6198_);
v___x_6200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6199_);
lean_ctor_set(v___x_6200_, 1, v___x_5898_);
v___x_6201_ = l_Bool_repr___redArg(v_instances_5897_);
v___x_6202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_5984_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
v___x_6203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set_uint8(v___x_6203_, sizeof(void*)*1, v___x_5904_);
v___x_6204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6200_);
lean_ctor_set(v___x_6204_, 1, v___x_6203_);
v___x_6205_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6206_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
lean_ctor_set(v___x_6207_, 1, v___x_6204_);
v___x_6208_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6207_);
lean_ctor_set(v___x_6209_, 1, v___x_6208_);
v___x_6210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6205_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
lean_ctor_set_uint8(v___x_6211_, sizeof(void*)*1, v___x_5904_);
return v___x_6211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6212_, lean_object* v_prec_6213_){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6212_);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6215_, lean_object* v_prec_6216_){
_start:
{
lean_object* v_res_6217_; 
v_res_6217_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6215_, v_prec_6216_);
lean_dec(v_prec_6216_);
return v_res_6217_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6220_, lean_object* v_x_6221_){
_start:
{
if (lean_obj_tag(v_x_6221_) == 0)
{
uint8_t v___x_6222_; 
v___x_6222_ = 0;
return v___x_6222_;
}
else
{
lean_object* v_head_6223_; lean_object* v_tail_6224_; uint8_t v___x_6225_; 
v_head_6223_ = lean_ctor_get(v_x_6221_, 0);
v_tail_6224_ = lean_ctor_get(v_x_6221_, 1);
v___x_6225_ = lean_nat_dec_eq(v_a_6220_, v_head_6223_);
if (v___x_6225_ == 0)
{
v_x_6221_ = v_tail_6224_;
goto _start;
}
else
{
return v___x_6225_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6227_, lean_object* v_x_6228_){
_start:
{
uint8_t v_res_6229_; lean_object* v_r_6230_; 
v_res_6229_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6227_, v_x_6228_);
lean_dec(v_x_6228_);
lean_dec(v_a_6227_);
v_r_6230_ = lean_box(v_res_6229_);
return v_r_6230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6231_, lean_object* v_x_6232_){
_start:
{
switch(lean_obj_tag(v_x_6231_))
{
case 0:
{
uint8_t v___x_6233_; 
v___x_6233_ = 1;
return v___x_6233_;
}
case 1:
{
lean_object* v_idxs_6234_; uint8_t v___x_6235_; 
v_idxs_6234_ = lean_ctor_get(v_x_6231_, 0);
v___x_6235_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6232_, v_idxs_6234_);
return v___x_6235_;
}
default: 
{
lean_object* v_idxs_6236_; uint8_t v___x_6237_; 
v_idxs_6236_ = lean_ctor_get(v_x_6231_, 0);
v___x_6237_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6232_, v_idxs_6236_);
if (v___x_6237_ == 0)
{
uint8_t v___x_6238_; 
v___x_6238_ = 1;
return v___x_6238_;
}
else
{
uint8_t v___x_6239_; 
v___x_6239_ = 0;
return v___x_6239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6240_, lean_object* v_x_6241_){
_start:
{
uint8_t v_res_6242_; lean_object* v_r_6243_; 
v_res_6242_ = l_Lean_Meta_Occurrences_contains(v_x_6240_, v_x_6241_);
lean_dec(v_x_6241_);
lean_dec(v_x_6240_);
v_r_6243_ = lean_box(v_res_6242_);
return v_r_6243_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6244_){
_start:
{
if (lean_obj_tag(v_x_6244_) == 0)
{
uint8_t v___x_6245_; 
v___x_6245_ = 1;
return v___x_6245_;
}
else
{
uint8_t v___x_6246_; 
v___x_6246_ = 0;
return v___x_6246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6247_){
_start:
{
uint8_t v_res_6248_; lean_object* v_r_6249_; 
v_res_6248_ = l_Lean_Meta_Occurrences_isAll(v_x_6247_);
lean_dec(v_x_6247_);
v_r_6249_ = lean_box(v_res_6248_);
return v_r_6249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(uint8_t v_x_6250_){
_start:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6251_ = lean_box(v_x_6250_);
v___x_6252_ = lean_obj_tag_nat(v___x_6251_);
lean_dec(v___x_6251_);
return v___x_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl___boxed(lean_object* v_x_6253_){
_start:
{
uint8_t v_x_4__boxed_6254_; lean_object* v_res_6255_; 
v_x_4__boxed_6254_ = lean_unbox(v_x_6253_);
v_res_6255_ = l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(v_x_4__boxed_6254_);
return v_res_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6256_){
_start:
{
lean_inc(v_k_6256_);
return v_k_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6257_){
_start:
{
lean_object* v_res_6258_; 
v_res_6258_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6257_);
lean_dec(v_k_6257_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6259_, lean_object* v_ctorIdx_6260_, uint8_t v_t_6261_, lean_object* v_h_6262_, lean_object* v_k_6263_){
_start:
{
lean_inc(v_k_6263_);
return v_k_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6264_, lean_object* v_ctorIdx_6265_, lean_object* v_t_6266_, lean_object* v_h_6267_, lean_object* v_k_6268_){
_start:
{
uint8_t v_t_boxed_6269_; lean_object* v_res_6270_; 
v_t_boxed_6269_ = lean_unbox(v_t_6266_);
v_res_6270_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6264_, v_ctorIdx_6265_, v_t_boxed_6269_, v_h_6267_, v_k_6268_);
lean_dec(v_k_6268_);
lean_dec(v_ctorIdx_6265_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6271_){
_start:
{
lean_inc(v_nonDependentFirst_6271_);
return v_nonDependentFirst_6271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6272_){
_start:
{
lean_object* v_res_6273_; 
v_res_6273_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6272_);
lean_dec(v_nonDependentFirst_6272_);
return v_res_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6274_, uint8_t v_t_6275_, lean_object* v_h_6276_, lean_object* v_nonDependentFirst_6277_){
_start:
{
lean_inc(v_nonDependentFirst_6277_);
return v_nonDependentFirst_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6278_, lean_object* v_t_6279_, lean_object* v_h_6280_, lean_object* v_nonDependentFirst_6281_){
_start:
{
uint8_t v_t_boxed_6282_; lean_object* v_res_6283_; 
v_t_boxed_6282_ = lean_unbox(v_t_6279_);
v_res_6283_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6278_, v_t_boxed_6282_, v_h_6280_, v_nonDependentFirst_6281_);
lean_dec(v_nonDependentFirst_6281_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6284_){
_start:
{
lean_inc(v_nonDependentOnly_6284_);
return v_nonDependentOnly_6284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6285_){
_start:
{
lean_object* v_res_6286_; 
v_res_6286_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6285_);
lean_dec(v_nonDependentOnly_6285_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6287_, uint8_t v_t_6288_, lean_object* v_h_6289_, lean_object* v_nonDependentOnly_6290_){
_start:
{
lean_inc(v_nonDependentOnly_6290_);
return v_nonDependentOnly_6290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6291_, lean_object* v_t_6292_, lean_object* v_h_6293_, lean_object* v_nonDependentOnly_6294_){
_start:
{
uint8_t v_t_boxed_6295_; lean_object* v_res_6296_; 
v_t_boxed_6295_ = lean_unbox(v_t_6292_);
v_res_6296_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6291_, v_t_boxed_6295_, v_h_6293_, v_nonDependentOnly_6294_);
lean_dec(v_nonDependentOnly_6294_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6297_){
_start:
{
lean_inc(v_all_6297_);
return v_all_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6298_){
_start:
{
lean_object* v_res_6299_; 
v_res_6299_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6298_);
lean_dec(v_all_6298_);
return v_res_6299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6300_, uint8_t v_t_6301_, lean_object* v_h_6302_, lean_object* v_all_6303_){
_start:
{
lean_inc(v_all_6303_);
return v_all_6303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6304_, lean_object* v_t_6305_, lean_object* v_h_6306_, lean_object* v_all_6307_){
_start:
{
uint8_t v_t_boxed_6308_; lean_object* v_res_6309_; 
v_t_boxed_6308_ = lean_unbox(v_t_6305_);
v_res_6309_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6304_, v_t_boxed_6308_, v_h_6306_, v_all_6307_);
lean_dec(v_all_6307_);
return v_res_6309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6323_){
_start:
{
lean_object* v___x_6324_; uint8_t v___x_6325_; 
v___x_6324_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6323_);
v___x_6325_ = l_Lean_Syntax_isOfKind(v_c_6323_, v___x_6324_);
if (v___x_6325_ == 0)
{
lean_object* v___x_6326_; uint8_t v___x_6327_; 
v___x_6326_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6323_);
v___x_6327_ = l_Lean_Syntax_isOfKind(v_c_6323_, v___x_6326_);
if (v___x_6327_ == 0)
{
lean_object* v___x_6328_; uint8_t v___x_6329_; 
v___x_6328_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6323_);
v___x_6329_ = l_Lean_Syntax_isOfKind(v_c_6323_, v___x_6328_);
if (v___x_6329_ == 0)
{
lean_object* v___x_6330_; 
lean_dec(v_c_6323_);
v___x_6330_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6330_;
}
else
{
lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; 
v___x_6331_ = lean_unsigned_to_nat(1u);
v___x_6332_ = lean_mk_empty_array_with_capacity(v___x_6331_);
v___x_6333_ = lean_array_push(v___x_6332_, v_c_6323_);
return v___x_6333_;
}
}
else
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6334_ = lean_unsigned_to_nat(0u);
v___x_6335_ = l_Lean_Syntax_getArg(v_c_6323_, v___x_6334_);
lean_dec(v_c_6323_);
v___x_6336_ = l_Lean_Syntax_getArgs(v___x_6335_);
lean_dec(v___x_6335_);
return v___x_6336_;
}
}
else
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; uint8_t v___x_6341_; 
v___x_6337_ = l_Lean_Syntax_getArgs(v_c_6323_);
lean_dec(v_c_6323_);
v___x_6338_ = lean_unsigned_to_nat(0u);
v___x_6339_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6340_ = lean_array_get_size(v___x_6337_);
v___x_6341_ = lean_nat_dec_lt(v___x_6338_, v___x_6340_);
if (v___x_6341_ == 0)
{
lean_dec_ref(v___x_6337_);
return v___x_6339_;
}
else
{
size_t v___x_6342_; size_t v___x_6343_; lean_object* v___x_6344_; 
v___x_6342_ = ((size_t)0ULL);
v___x_6343_ = lean_usize_of_nat(v___x_6340_);
v___x_6344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6337_, v___x_6342_, v___x_6343_, v___x_6339_);
lean_dec_ref(v___x_6337_);
return v___x_6344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6345_, size_t v_i_6346_, size_t v_stop_6347_, lean_object* v_b_6348_){
_start:
{
uint8_t v___x_6349_; 
v___x_6349_ = lean_usize_dec_eq(v_i_6346_, v_stop_6347_);
if (v___x_6349_ == 0)
{
lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; size_t v___x_6353_; size_t v___x_6354_; 
v___x_6350_ = lean_array_uget_borrowed(v_as_6345_, v_i_6346_);
lean_inc(v___x_6350_);
v___x_6351_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6350_);
v___x_6352_ = l_Array_append___redArg(v_b_6348_, v___x_6351_);
lean_dec_ref(v___x_6351_);
v___x_6353_ = ((size_t)1ULL);
v___x_6354_ = lean_usize_add(v_i_6346_, v___x_6353_);
v_i_6346_ = v___x_6354_;
v_b_6348_ = v___x_6352_;
goto _start;
}
else
{
return v_b_6348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6356_, lean_object* v_i_6357_, lean_object* v_stop_6358_, lean_object* v_b_6359_){
_start:
{
size_t v_i_boxed_6360_; size_t v_stop_boxed_6361_; lean_object* v_res_6362_; 
v_i_boxed_6360_ = lean_unbox_usize(v_i_6357_);
lean_dec(v_i_6357_);
v_stop_boxed_6361_ = lean_unbox_usize(v_stop_6358_);
lean_dec(v_stop_6358_);
v_res_6362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6356_, v_i_boxed_6360_, v_stop_boxed_6361_, v_b_6359_);
lean_dec_ref(v_as_6356_);
return v_res_6362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6363_){
_start:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6364_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6365_ = lean_box(2);
v___x_6366_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6367_, 0, v___x_6365_);
lean_ctor_set(v___x_6367_, 1, v___x_6366_);
lean_ctor_set(v___x_6367_, 2, v_items_6363_);
v___x_6368_ = l_Lean_Syntax_node1(v___x_6365_, v___x_6364_, v___x_6367_);
return v___x_6368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6369_, lean_object* v_cfg_x27_6370_){
_start:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; 
v___x_6371_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6369_);
v___x_6372_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6370_);
v___x_6373_ = l_Array_append___redArg(v___x_6371_, v___x_6372_);
lean_dec_ref(v___x_6372_);
v___x_6374_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6373_);
return v___x_6374_;
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
