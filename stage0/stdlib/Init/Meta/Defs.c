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
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Init.Meta.Defs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Substring.Raw.toName"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3699_ = lean_unsigned_to_nat(10u);
v___x_3700_ = lean_unsigned_to_nat(1257u);
v___x_3701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3703_ = l_mkPanicMessageWithDecl(v___x_3702_, v___x_3701_, v___x_3700_, v___x_3699_, v___x_3698_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(lean_object* v_as_3704_, size_t v_i_3705_, size_t v_stop_3706_, lean_object* v_b_3707_){
_start:
{
uint8_t v___x_3708_; 
v___x_3708_ = lean_usize_dec_eq(v_i_3705_, v_stop_3706_);
if (v___x_3708_ == 0)
{
size_t v___x_3709_; size_t v___x_3710_; lean_object* v___x_3711_; lean_object* v_comp_3712_; uint32_t v___x_3713_; uint32_t v___x_3714_; uint8_t v___x_3715_; 
v___x_3709_ = ((size_t)1ULL);
v___x_3710_ = lean_usize_sub(v_i_3705_, v___x_3709_);
v___x_3711_ = lean_array_uget_borrowed(v_as_3704_, v___x_3710_);
lean_inc(v___x_3711_);
v_comp_3712_ = lean_substring_tostring(v___x_3711_);
lean_inc_ref(v_comp_3712_);
v___x_3713_ = lean_string_front(v_comp_3712_);
v___x_3714_ = 171;
v___x_3715_ = lean_uint32_dec_eq(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
uint32_t v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = 48;
v___x_3717_ = lean_uint32_dec_le(v___x_3716_, v___x_3713_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_Name_str___override(v_b_3707_, v_comp_3712_);
v_i_3705_ = v___x_3710_;
v_b_3707_ = v___x_3718_;
goto _start;
}
else
{
uint32_t v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = 57;
v___x_3721_ = lean_uint32_dec_le(v___x_3713_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Name_str___override(v_b_3707_, v_comp_3712_);
v_i_3705_ = v___x_3710_;
v_b_3707_ = v___x_3722_;
goto _start;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3712_);
lean_dec_ref(v_comp_3712_);
if (lean_obj_tag(v___x_3724_) == 1)
{
lean_object* v_val_3725_; lean_object* v___x_3726_; 
v_val_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_val_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = l_Lean_Name_num___override(v_b_3707_, v_val_3725_);
v_i_3705_ = v___x_3710_;
v_b_3707_ = v___x_3726_;
goto _start;
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec(v___x_3724_);
lean_dec(v_b_3707_);
v___x_3728_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3729_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3728_);
v_i_3705_ = v___x_3710_;
v_b_3707_ = v___x_3729_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3731_ = lean_unsigned_to_nat(1u);
v___x_3732_ = lean_string_drop(v_comp_3712_, v___x_3731_);
v___x_3733_ = lean_string_dropright(v___x_3732_, v___x_3731_);
v___x_3734_ = l_Lean_Name_str___override(v_b_3707_, v___x_3733_);
v_i_3705_ = v___x_3710_;
v_b_3707_ = v___x_3734_;
goto _start;
}
}
else
{
return v_b_3707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_as_3736_, lean_object* v_i_3737_, lean_object* v_stop_3738_, lean_object* v_b_3739_){
_start:
{
size_t v_i_boxed_3740_; size_t v_stop_boxed_3741_; lean_object* v_res_3742_; 
v_i_boxed_3740_ = lean_unbox_usize(v_i_3737_);
lean_dec(v_i_3737_);
v_stop_boxed_3741_ = lean_unbox_usize(v_stop_3738_);
lean_dec(v_stop_3738_);
v_res_3742_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(v_as_3736_, v_i_boxed_3740_, v_stop_boxed_3741_, v_b_3739_);
lean_dec_ref(v_as_3736_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3743_){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_box(0);
v___x_3745_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3743_, v___x_3744_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_box(0);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3747_ = lean_box(0);
v___x_3748_ = lean_array_mk(v___x_3745_);
v___x_3749_ = lean_array_get_size(v___x_3748_);
v___x_3750_ = lean_unsigned_to_nat(0u);
v___x_3751_ = lean_nat_dec_lt(v___x_3750_, v___x_3749_);
if (v___x_3751_ == 0)
{
lean_dec_ref(v___x_3748_);
return v___x_3747_;
}
else
{
size_t v___x_3752_; size_t v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_usize_of_nat(v___x_3749_);
v___x_3753_ = ((size_t)0ULL);
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(v___x_3748_, v___x_3752_, v___x_3753_, v___x_3747_);
lean_dec_ref(v___x_3748_);
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3755_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = lean_string_utf8_byte_size(v_s_3755_);
v___x_3758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3758_, 0, v_s_3755_);
lean_ctor_set(v___x_3758_, 1, v___x_3756_);
lean_ctor_set(v___x_3758_, 2, v___x_3757_);
v___x_3759_ = l_Substring_Raw_toName(v___x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3760_){
_start:
{
lean_object* v___x_3761_; uint32_t v___x_3762_; uint32_t v___x_3763_; uint8_t v___x_3764_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_string_utf8_get(v_s_3760_, v___x_3761_);
v___x_3763_ = 96;
v___x_3764_ = lean_uint32_dec_eq(v___x_3762_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; 
lean_dec_ref(v_s_3760_);
v___x_3765_ = lean_box(0);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3766_ = lean_string_utf8_byte_size(v_s_3760_);
v___x_3767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3767_, 0, v_s_3760_);
lean_ctor_set(v___x_3767_, 1, v___x_3761_);
lean_ctor_set(v___x_3767_, 2, v___x_3766_);
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_substring_drop(v___x_3767_, v___x_3768_);
v___x_3770_ = l_Substring_Raw_toName(v___x_3769_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_box(0);
return v___x_3771_;
}
else
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
return v___x_3772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3773_){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3775_ = l_Lean_Syntax_isLit_x3f(v___x_3774_, v_stx_3773_);
if (lean_obj_tag(v___x_3775_) == 1)
{
lean_object* v_val_3776_; lean_object* v___x_3777_; 
v_val_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3777_ = l_Lean_Syntax_decodeNameLit(v_val_3776_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; 
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
return v___x_3778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3779_);
lean_dec(v_stx_3779_);
return v_res_3780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3781_){
_start:
{
if (lean_obj_tag(v_x_3781_) == 1)
{
lean_object* v_args_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v_args_3782_ = lean_ctor_get(v_x_3781_, 2);
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = lean_array_get_size(v_args_3782_);
v___x_3785_ = lean_nat_dec_lt(v___x_3783_, v___x_3784_);
return v___x_3785_;
}
else
{
uint8_t v___x_3786_; 
v___x_3786_ = 0;
return v___x_3786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3787_){
_start:
{
uint8_t v_res_3788_; lean_object* v_r_3789_; 
v_res_3788_ = l_Lean_Syntax_hasArgs(v_x_3787_);
lean_dec(v_x_3787_);
v_r_3789_ = lean_box(v_res_3788_);
return v_r_3789_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 2)
{
uint8_t v___x_3791_; 
v___x_3791_ = 1;
return v___x_3791_;
}
else
{
uint8_t v___x_3792_; 
v___x_3792_ = 0;
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3793_){
_start:
{
uint8_t v_res_3794_; lean_object* v_r_3795_; 
v_res_3794_ = l_Lean_Syntax_isAtom(v_x_3793_);
lean_dec(v_x_3793_);
v_r_3795_ = lean_box(v_res_3794_);
return v_r_3795_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3796_, lean_object* v_x_3797_){
_start:
{
if (lean_obj_tag(v_x_3797_) == 2)
{
lean_object* v_val_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v_val_3798_ = lean_ctor_get(v_x_3797_, 1);
lean_inc_ref(v_val_3798_);
lean_dec_ref_known(v_x_3797_, 2);
v___x_3799_ = lean_string_trim(v_val_3798_);
v___x_3800_ = lean_string_trim(v_token_3796_);
v___x_3801_ = lean_string_dec_eq(v___x_3799_, v___x_3800_);
lean_dec_ref(v___x_3800_);
lean_dec_ref(v___x_3799_);
return v___x_3801_;
}
else
{
uint8_t v___x_3802_; 
lean_dec(v_x_3797_);
lean_dec_ref(v_token_3796_);
v___x_3802_ = 0;
return v___x_3802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3803_, lean_object* v_x_3804_){
_start:
{
uint8_t v_res_3805_; lean_object* v_r_3806_; 
v_res_3805_ = l_Lean_Syntax_isToken(v_token_3803_, v_x_3804_);
v_r_3806_ = lean_box(v_res_3805_);
return v_r_3806_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3807_){
_start:
{
switch(lean_obj_tag(v_stx_3807_))
{
case 1:
{
lean_object* v_kind_3808_; lean_object* v_args_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_kind_3808_ = lean_ctor_get(v_stx_3807_, 1);
v_args_3809_ = lean_ctor_get(v_stx_3807_, 2);
v___x_3810_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3811_ = lean_name_eq(v_kind_3808_, v___x_3810_);
if (v___x_3811_ == 0)
{
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3812_ = lean_array_get_size(v_args_3809_);
v___x_3813_ = lean_unsigned_to_nat(0u);
v___x_3814_ = lean_nat_dec_eq(v___x_3812_, v___x_3813_);
return v___x_3814_;
}
}
case 0:
{
uint8_t v___x_3815_; 
v___x_3815_ = 1;
return v___x_3815_;
}
default: 
{
uint8_t v___x_3816_; 
v___x_3816_ = 0;
return v___x_3816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3817_){
_start:
{
uint8_t v_res_3818_; lean_object* v_r_3819_; 
v_res_3818_ = l_Lean_Syntax_isNone(v_stx_3817_);
lean_dec(v_stx_3817_);
v_r_3819_ = lean_box(v_res_3818_);
return v_r_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_Syntax_getOptional_x3f(v_stx_3820_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_box(0);
return v___x_3822_;
}
else
{
lean_object* v_val_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3831_; 
v_val_3823_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3825_ = v___x_3821_;
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_val_3823_);
lean_dec(v___x_3821_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = l_Lean_Syntax_getId(v_val_3823_);
lean_dec(v_val_3823_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3832_);
lean_dec(v_stx_3832_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3834_, lean_object* v_x_3835_){
_start:
{
if (lean_obj_tag(v_x_3835_) == 1)
{
lean_object* v_args_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v_args_3836_ = lean_ctor_get(v_x_3835_, 2);
lean_inc_ref(v_p_3834_);
lean_inc_ref(v_x_3835_);
v___x_3837_ = lean_apply_1(v_p_3834_, v_x_3835_);
v___x_3838_ = lean_unbox(v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; size_t v_sz_3841_; size_t v___x_3842_; lean_object* v___x_3843_; lean_object* v_fst_3844_; 
lean_inc_ref(v_args_3836_);
lean_dec_ref_known(v_x_3835_, 3);
v___x_3839_ = lean_box(0);
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3841_ = lean_array_size(v_args_3836_);
v___x_3842_ = ((size_t)0ULL);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3834_, v_args_3836_, v_sz_3841_, v___x_3842_, v___x_3840_);
lean_dec_ref(v_args_3836_);
v_fst_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_fst_3844_);
lean_dec_ref(v___x_3843_);
if (lean_obj_tag(v_fst_3844_) == 0)
{
return v___x_3839_;
}
else
{
lean_object* v_val_3845_; 
v_val_3845_ = lean_ctor_get(v_fst_3844_, 0);
lean_inc(v_val_3845_);
lean_dec_ref_known(v_fst_3844_, 1);
return v_val_3845_;
}
}
else
{
lean_object* v___x_3846_; 
lean_dec_ref(v_p_3834_);
v___x_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_x_3835_);
return v___x_3846_;
}
}
else
{
lean_object* v___x_3847_; uint8_t v___x_3848_; 
lean_inc(v_x_3835_);
v___x_3847_ = lean_apply_1(v_p_3834_, v_x_3835_);
v___x_3848_ = lean_unbox(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
lean_dec(v_x_3835_);
v___x_3849_ = lean_box(0);
return v___x_3849_;
}
else
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v_x_3835_);
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3851_, lean_object* v_as_3852_, size_t v_sz_3853_, size_t v_i_3854_, lean_object* v_b_3855_){
_start:
{
uint8_t v___x_3856_; 
v___x_3856_ = lean_usize_dec_lt(v_i_3854_, v_sz_3853_);
if (v___x_3856_ == 0)
{
lean_dec_ref(v_p_3851_);
lean_inc_ref(v_b_3855_);
return v_b_3855_;
}
else
{
lean_object* v___x_3857_; lean_object* v_a_3858_; lean_object* v___x_3859_; 
v___x_3857_ = lean_box(0);
v_a_3858_ = lean_array_uget_borrowed(v_as_3852_, v_i_3854_);
lean_inc(v_a_3858_);
lean_inc_ref(v_p_3851_);
v___x_3859_ = l_Lean_Syntax_findAux(v_p_3851_, v_a_3858_);
if (lean_obj_tag(v___x_3859_) == 1)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
lean_dec_ref(v_p_3851_);
v___x_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3857_);
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; 
lean_dec(v___x_3859_);
v___x_3862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3863_ = ((size_t)1ULL);
v___x_3864_ = lean_usize_add(v_i_3854_, v___x_3863_);
v_i_3854_ = v___x_3864_;
v_b_3855_ = v___x_3862_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3866_, lean_object* v_as_3867_, lean_object* v_sz_3868_, lean_object* v_i_3869_, lean_object* v_b_3870_){
_start:
{
size_t v_sz_boxed_3871_; size_t v_i_boxed_3872_; lean_object* v_res_3873_; 
v_sz_boxed_3871_ = lean_unbox_usize(v_sz_3868_);
lean_dec(v_sz_3868_);
v_i_boxed_3872_ = lean_unbox_usize(v_i_3869_);
lean_dec(v_i_3869_);
v_res_3873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3866_, v_as_3867_, v_sz_boxed_3871_, v_i_boxed_3872_, v_b_3870_);
lean_dec_ref(v_b_3870_);
lean_dec_ref(v_as_3867_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3874_, lean_object* v_p_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_Syntax_findAux(v_p_3875_, v_stx_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Lean_Syntax_isNatLit_x3f(v_s_3877_);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_TSyntax_getNat(v_s_3881_);
lean_dec(v_s_3881_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3886_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3888_ = l_Lean_Syntax_isLit_x3f(v___x_3887_, v_stx_3886_);
if (lean_obj_tag(v___x_3888_) == 1)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_val_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3890_ = lean_unsigned_to_nat(0u);
v___x_3891_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3889_, v___x_3890_, v___x_3890_);
lean_dec(v_val_3889_);
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; 
lean_dec(v___x_3888_);
v___x_3892_ = lean_box(0);
return v___x_3892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3893_);
lean_dec(v_stx_3893_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3895_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_unsigned_to_nat(0u);
return v___x_3897_;
}
else
{
lean_object* v_val_3898_; 
v_val_3898_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v___x_3896_, 1);
return v_val_3898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_TSyntax_getHexNumVal(v_s_3899_);
lean_dec(v_s_3899_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3901_, lean_object* v_p_3902_, lean_object* v_n_3903_){
_start:
{
uint8_t v___x_3904_; 
v___x_3904_ = lean_string_utf8_at_end(v_s_3901_, v_p_3902_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; uint32_t v___x_3906_; uint32_t v___x_3907_; uint8_t v___x_3908_; 
v___x_3905_ = lean_string_utf8_next(v_s_3901_, v_p_3902_);
v___x_3906_ = lean_string_utf8_get(v_s_3901_, v_p_3902_);
lean_dec(v_p_3902_);
v___x_3907_ = 95;
v___x_3908_ = lean_uint32_dec_eq(v___x_3906_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_add(v_n_3903_, v___x_3909_);
lean_dec(v_n_3903_);
v_p_3902_ = v___x_3905_;
v_n_3903_ = v___x_3910_;
goto _start;
}
else
{
v_p_3902_ = v___x_3905_;
goto _start;
}
}
else
{
lean_dec(v_p_3902_);
return v_n_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3913_, lean_object* v_p_3914_, lean_object* v_n_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3913_, v_p_3914_, v_n_3915_);
lean_dec_ref(v_s_3913_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3917_){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3919_ = l_Lean_Syntax_isLit_x3f(v___x_3918_, v_s_3917_);
if (lean_obj_tag(v___x_3919_) == 1)
{
lean_object* v_val_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_val_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_val_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3921_ = lean_unsigned_to_nat(0u);
v___x_3922_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3920_, v___x_3921_, v___x_3921_);
lean_dec(v_val_3920_);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; 
lean_dec(v___x_3919_);
v___x_3923_ = lean_unsigned_to_nat(0u);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_TSyntax_getHexNumSize(v_s_3924_);
lean_dec(v_s_3924_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Syntax_getId(v_s_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_TSyntax_getId(v_s_3928_);
lean_dec(v_s_3928_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3937_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v___x_3939_; 
v___x_3939_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3939_;
}
else
{
lean_object* v_val_3940_; 
v_val_3940_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_val_3940_);
lean_dec_ref_known(v___x_3938_, 1);
return v_val_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_TSyntax_getScientific(v_s_3941_);
lean_dec(v_s_3941_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3943_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_Syntax_isStrLit_x3f(v_s_3943_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v___x_3945_; 
v___x_3945_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3945_;
}
else
{
lean_object* v_val_3946_; 
v_val_3946_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_val_3946_);
lean_dec_ref_known(v___x_3944_, 1);
return v_val_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_TSyntax_getString(v_s_3947_);
lean_dec(v_s_3947_);
return v_res_3948_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Syntax_isCharLit_x3f(v_s_3949_);
if (lean_obj_tag(v___x_3950_) == 0)
{
uint32_t v___x_3951_; 
v___x_3951_ = 65;
return v___x_3951_;
}
else
{
lean_object* v_val_3952_; uint32_t v___x_3953_; 
v_val_3952_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_val_3952_);
lean_dec_ref_known(v___x_3950_, 1);
v___x_3953_ = lean_unbox_uint32(v_val_3952_);
lean_dec(v_val_3952_);
return v___x_3953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3954_){
_start:
{
uint32_t v_res_3955_; lean_object* v_r_3956_; 
v_res_3955_ = l_Lean_TSyntax_getChar(v_s_3954_);
lean_dec(v_s_3954_);
v_r_3956_ = lean_box_uint32(v_res_3955_);
return v_r_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Syntax_isNameLit_x3f(v_s_3957_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_box(0);
return v___x_3959_;
}
else
{
lean_object* v_val_3960_; 
v_val_3960_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_val_3960_);
lean_dec_ref_known(v___x_3958_, 1);
return v_val_3960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_TSyntax_getName(v_s_3961_);
lean_dec(v_s_3961_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3963_){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3964_ = lean_unsigned_to_nat(0u);
v___x_3965_ = l_Lean_Syntax_getArg(v_s_3963_, v___x_3964_);
v___x_3966_ = l_Lean_Syntax_getId(v___x_3965_);
lean_dec(v___x_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_TSyntax_getHygieneInfo(v_s_3967_);
lean_dec(v_s_3967_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3969_, v_a_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3972_, v_a_3973_);
lean_dec_ref(v_a_3973_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3975_){
_start:
{
lean_object* v___f_3976_; 
v___f_3976_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3976_, 0, v_sep_3975_);
return v___f_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3977_, lean_object* v_sep_3978_){
_start:
{
lean_object* v___f_3979_; 
v___f_3979_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3979_, 0, v_sep_3978_);
return v___f_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3980_, lean_object* v_sep_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3980_, v_sep_3981_);
lean_dec(v_k_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3983_, lean_object* v_val_3984_, uint8_t v_canonical_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v_src_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v_imported_3990_; lean_object* v_ctx_3991_; lean_object* v_scopes_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4008_; 
v___x_3986_ = lean_unsigned_to_nat(0u);
v_src_3987_ = l_Lean_Syntax_getArg(v_s_3983_, v___x_3986_);
v___x_3988_ = l_Lean_Syntax_getId(v_src_3987_);
v___x_3989_ = l_Lean_extractMacroScopes(v___x_3988_);
v_imported_3990_ = lean_ctor_get(v___x_3989_, 1);
v_ctx_3991_ = lean_ctor_get(v___x_3989_, 2);
v_scopes_3992_ = lean_ctor_get(v___x_3989_, 3);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v___x_3989_, 0);
lean_dec(v_unused_4009_);
v___x_3994_ = v___x_3989_;
v_isShared_3995_ = v_isSharedCheck_4008_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_scopes_3992_);
lean_inc(v_ctx_3991_);
lean_inc(v_imported_3990_);
lean_dec(v___x_3989_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4008_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3996_ = l_Lean_Name_eraseMacroScopes(v_val_3984_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 0, v___x_3996_);
v___x_3998_ = v___x_3994_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_imported_3990_);
lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_ctx_3991_);
lean_ctor_set(v_reuseFailAlloc_4007_, 3, v_scopes_3992_);
v___x_3998_ = v_reuseFailAlloc_4007_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v_id_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v_id_3999_ = l_Lean_MacroScopesView_review(v___x_3998_);
v___x_4000_ = l_Lean_SourceInfo_fromRef(v_src_3987_, v_canonical_3985_);
lean_dec(v_src_3987_);
v___x_4001_ = 1;
v___x_4002_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3984_, v___x_4001_);
v___x_4003_ = lean_string_utf8_byte_size(v___x_4002_);
v___x_4004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4002_);
lean_ctor_set(v___x_4004_, 1, v___x_3986_);
lean_ctor_set(v___x_4004_, 2, v___x_4003_);
v___x_4005_ = lean_box(0);
v___x_4006_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4000_);
lean_ctor_set(v___x_4006_, 1, v___x_4004_);
lean_ctor_set(v___x_4006_, 2, v_id_3999_);
lean_ctor_set(v___x_4006_, 3, v___x_4005_);
return v___x_4006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4010_, lean_object* v_val_4011_, lean_object* v_canonical_4012_){
_start:
{
uint8_t v_canonical_boxed_4013_; lean_object* v_res_4014_; 
v_canonical_boxed_4013_ = lean_unbox(v_canonical_4012_);
v_res_4014_ = l_Lean_HygieneInfo_mkIdent(v_s_4010_, v_val_4011_, v_canonical_boxed_4013_);
lean_dec(v_s_4010_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4015_, lean_object* v_inst_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = lean_apply_1(v_inst_4015_, v_a_4017_);
v___x_4019_ = lean_apply_1(v_inst_4016_, v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4020_, lean_object* v_inst_4021_){
_start:
{
lean_object* v___f_4022_; 
v___f_4022_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4022_, 0, v_inst_4020_);
lean_closure_set(v___f_4022_, 1, v_inst_4021_);
return v___f_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4023_, lean_object* v_k_4024_, lean_object* v_k_x27_4025_, lean_object* v_inst_4026_, lean_object* v_inst_4027_){
_start:
{
lean_object* v___f_4028_; 
v___f_4028_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4028_, 0, v_inst_4026_);
lean_closure_set(v___f_4028_, 1, v_inst_4027_);
return v___f_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4029_, lean_object* v_k_4030_, lean_object* v_k_x27_4031_, lean_object* v_inst_4032_, lean_object* v_inst_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4029_, v_k_4030_, v_k_x27_4031_, v_inst_4032_, v_inst_4033_);
lean_dec(v_k_x27_4031_);
lean_dec(v_k_4030_);
return v_res_4034_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4043_ = l_Lean_mkCIdent(v___x_4042_);
return v___x_4043_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4049_ = l_Lean_mkCIdent(v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4050_){
_start:
{
if (v_x_4050_ == 0)
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4051_;
}
else
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4053_){
_start:
{
uint8_t v_x_85__boxed_4054_; lean_object* v_res_4055_; 
v_x_85__boxed_4054_ = lean_unbox(v_x_4053_);
v_res_4055_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4054_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4058_){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_box(2);
v___x_4060_ = l_Lean_Syntax_mkCharLit(v_val_4058_, v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4061_){
_start:
{
uint32_t v_val_boxed_4062_; lean_object* v_res_4063_; 
v_val_boxed_4062_ = lean_unbox_uint32(v_val_4061_);
lean_dec(v_val_4061_);
v_res_4063_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4062_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4066_){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = lean_box(2);
v___x_4068_ = l_Lean_Syntax_mkStrLit(v_val_4066_, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = l_Nat_reprFast(v_n_4071_);
v___x_4073_ = lean_box(2);
v___x_4074_ = l_Lean_Syntax_mkNumLit(v___x_4072_, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4082_){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4083_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4084_ = lean_substring_tostring(v_s_4082_);
v___x_4085_ = lean_box(2);
v___x_4086_ = l_Lean_Syntax_mkStrLit(v___x_4084_, v___x_4085_);
v___x_4087_ = lean_unsigned_to_nat(1u);
v___x_4088_ = lean_mk_empty_array_with_capacity(v___x_4087_);
v___x_4089_ = lean_array_push(v___x_4088_, v___x_4086_);
v___x_4090_ = l_Lean_Syntax_mkCApp(v___x_4083_, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4093_, lean_object* v_x_4094_){
_start:
{
switch(lean_obj_tag(v_x_4094_))
{
case 0:
{
uint8_t v___x_4095_; 
v___x_4095_ = l_List_isEmpty___redArg(v_acc_4093_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_acc_4093_);
return v___x_4096_;
}
else
{
lean_object* v___x_4097_; 
lean_dec(v_acc_4093_);
v___x_4097_ = lean_box(0);
return v___x_4097_;
}
}
case 1:
{
lean_object* v_pre_4098_; lean_object* v_str_4099_; lean_object* v_val_4101_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v_pre_4098_ = lean_ctor_get(v_x_4094_, 0);
lean_inc(v_pre_4098_);
v_str_4099_ = lean_ctor_get(v_x_4094_, 1);
lean_inc_ref(v_str_4099_);
lean_dec_ref_known(v_x_4094_, 2);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_string_utf8_byte_size(v_str_4099_);
v___x_4106_ = lean_nat_dec_lt(v___x_4104_, v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4107_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4108_ = lean_string_append(v___x_4107_, v_str_4099_);
lean_dec_ref(v_str_4099_);
v___x_4109_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4110_ = lean_string_append(v___x_4108_, v___x_4109_);
v_val_4101_ = v___x_4110_;
goto v___jp_4100_;
}
else
{
lean_object* v___f_4111_; lean_object* v___f_4119_; uint32_t v___y_4126_; uint32_t v___y_4131_; uint8_t v_c_4145_; uint8_t v___x_4154_; uint8_t v___x_4155_; 
v___f_4111_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4119_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4145_ = lean_string_get_byte_fast(v_str_4099_, v___x_4104_);
v___x_4154_ = 97;
v___x_4155_ = lean_uint8_dec_le(v___x_4154_, v_c_4145_);
if (v___x_4155_ == 0)
{
goto v___jp_4149_;
}
else
{
uint8_t v___x_4156_; uint8_t v___x_4157_; 
v___x_4156_ = 122;
v___x_4157_ = lean_uint8_dec_le(v_c_4145_, v___x_4156_);
if (v___x_4157_ == 0)
{
goto v___jp_4149_;
}
else
{
goto v___jp_4142_;
}
}
v___jp_4112_:
{
uint8_t v___x_4113_; 
lean_inc_ref(v_str_4099_);
v___x_4113_ = lean_string_any(v_str_4099_, v___f_4111_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4114_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4115_ = lean_string_append(v___x_4114_, v_str_4099_);
lean_dec_ref(v_str_4099_);
v___x_4116_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
v_val_4101_ = v___x_4117_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4118_; 
lean_dec_ref(v_str_4099_);
lean_dec(v_pre_4098_);
lean_dec(v_acc_4093_);
v___x_4118_ = lean_box(0);
return v___x_4118_;
}
}
v___jp_4120_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; 
lean_inc_ref(v_str_4099_);
v___x_4121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4121_, 0, v_str_4099_);
lean_ctor_set(v___x_4121_, 1, v___x_4104_);
lean_ctor_set(v___x_4121_, 2, v___x_4105_);
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = lean_substring_drop(v___x_4121_, v___x_4122_);
v___x_4124_ = lean_substring_all(v___x_4123_, v___f_4119_);
if (v___x_4124_ == 0)
{
goto v___jp_4112_;
}
else
{
v_val_4101_ = v_str_4099_;
goto v___jp_4100_;
}
}
v___jp_4125_:
{
uint32_t v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = 95;
v___x_4128_ = lean_uint32_dec_eq(v___y_4126_, v___x_4127_);
if (v___x_4128_ == 0)
{
uint8_t v___x_4129_; 
v___x_4129_ = l_Lean_isLetterLike(v___y_4126_);
if (v___x_4129_ == 0)
{
goto v___jp_4112_;
}
else
{
goto v___jp_4120_;
}
}
else
{
goto v___jp_4120_;
}
}
v___jp_4130_:
{
uint32_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = 97;
v___x_4133_ = lean_uint32_dec_le(v___x_4132_, v___y_4131_);
if (v___x_4133_ == 0)
{
v___y_4126_ = v___y_4131_;
goto v___jp_4125_;
}
else
{
uint32_t v___x_4134_; uint8_t v___x_4135_; 
v___x_4134_ = 122;
v___x_4135_ = lean_uint32_dec_le(v___y_4131_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4126_ = v___y_4131_;
goto v___jp_4125_;
}
else
{
goto v___jp_4120_;
}
}
}
v___jp_4136_:
{
uint32_t v___x_4137_; uint32_t v___x_4138_; uint8_t v___x_4139_; 
v___x_4137_ = lean_string_utf8_get(v_str_4099_, v___x_4104_);
v___x_4138_ = 65;
v___x_4139_ = lean_uint32_dec_le(v___x_4138_, v___x_4137_);
if (v___x_4139_ == 0)
{
v___y_4131_ = v___x_4137_;
goto v___jp_4130_;
}
else
{
uint32_t v___x_4140_; uint8_t v___x_4141_; 
v___x_4140_ = 90;
v___x_4141_ = lean_uint32_dec_le(v___x_4137_, v___x_4140_);
if (v___x_4141_ == 0)
{
v___y_4131_ = v___x_4137_;
goto v___jp_4130_;
}
else
{
goto v___jp_4120_;
}
}
}
v___jp_4142_:
{
lean_object* v___x_4143_; uint8_t v___x_4144_; 
v___x_4143_ = lean_unsigned_to_nat(1u);
v___x_4144_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4099_, v___x_4143_);
if (v___x_4144_ == 0)
{
goto v___jp_4136_;
}
else
{
v_val_4101_ = v_str_4099_;
goto v___jp_4100_;
}
}
v___jp_4146_:
{
uint8_t v___x_4147_; uint8_t v___x_4148_; 
v___x_4147_ = 95;
v___x_4148_ = lean_uint8_dec_eq(v_c_4145_, v___x_4147_);
if (v___x_4148_ == 0)
{
goto v___jp_4136_;
}
else
{
goto v___jp_4142_;
}
}
v___jp_4149_:
{
uint8_t v___x_4150_; uint8_t v___x_4151_; 
v___x_4150_ = 65;
v___x_4151_ = lean_uint8_dec_le(v___x_4150_, v_c_4145_);
if (v___x_4151_ == 0)
{
goto v___jp_4146_;
}
else
{
uint8_t v___x_4152_; uint8_t v___x_4153_; 
v___x_4152_ = 90;
v___x_4153_ = lean_uint8_dec_le(v_c_4145_, v___x_4152_);
if (v___x_4153_ == 0)
{
goto v___jp_4146_;
}
else
{
goto v___jp_4142_;
}
}
}
}
v___jp_4100_:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4102_, 0, v_val_4101_);
lean_ctor_set(v___x_4102_, 1, v_acc_4093_);
v_acc_4093_ = v___x_4102_;
v_x_4094_ = v_pre_4098_;
goto _start;
}
}
default: 
{
lean_object* v___x_4158_; 
lean_dec_ref_known(v_x_4094_, 2);
lean_dec(v_acc_4093_);
v___x_4158_ = lean_box(0);
return v___x_4158_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4166_ = l_Lean_mkCIdent(v___x_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4177_){
_start:
{
switch(lean_obj_tag(v_x_4177_))
{
case 0:
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4178_;
}
case 1:
{
lean_object* v_pre_4179_; lean_object* v_str_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_pre_4179_ = lean_ctor_get(v_x_4177_, 0);
lean_inc(v_pre_4179_);
v_str_4180_ = lean_ctor_get(v_x_4177_, 1);
lean_inc_ref(v_str_4180_);
lean_dec_ref_known(v_x_4177_, 2);
v___x_4181_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4182_ = l_Lean_quoteNameMk(v_pre_4179_);
v___x_4183_ = lean_box(2);
v___x_4184_ = l_Lean_Syntax_mkStrLit(v_str_4180_, v___x_4183_);
v___x_4185_ = lean_unsigned_to_nat(2u);
v___x_4186_ = lean_mk_empty_array_with_capacity(v___x_4185_);
v___x_4187_ = lean_array_push(v___x_4186_, v___x_4182_);
v___x_4188_ = lean_array_push(v___x_4187_, v___x_4184_);
v___x_4189_ = l_Lean_Syntax_mkCApp(v___x_4181_, v___x_4188_);
return v___x_4189_;
}
default: 
{
lean_object* v_pre_4190_; lean_object* v_i_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_pre_4190_ = lean_ctor_get(v_x_4177_, 0);
lean_inc(v_pre_4190_);
v_i_4191_ = lean_ctor_get(v_x_4177_, 1);
lean_inc(v_i_4191_);
lean_dec_ref_known(v_x_4177_, 2);
v___x_4192_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4193_ = l_Lean_quoteNameMk(v_pre_4190_);
v___x_4194_ = l_Nat_reprFast(v_i_4191_);
v___x_4195_ = lean_box(2);
v___x_4196_ = l_Lean_Syntax_mkNumLit(v___x_4194_, v___x_4195_);
v___x_4197_ = lean_unsigned_to_nat(2u);
v___x_4198_ = lean_mk_empty_array_with_capacity(v___x_4197_);
v___x_4199_ = lean_array_push(v___x_4198_, v___x_4193_);
v___x_4200_ = lean_array_push(v___x_4199_, v___x_4196_);
v___x_4201_ = l_Lean_Syntax_mkCApp(v___x_4192_, v___x_4200_);
return v___x_4201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4208_){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = lean_box(0);
lean_inc(v_n_4208_);
v___x_4210_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4209_, v_n_4208_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_quoteNameMk(v_n_4208_);
return v___x_4211_;
}
else
{
lean_object* v_val_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
lean_dec(v_n_4208_);
v_val_4212_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_val_4212_);
lean_dec_ref_known(v___x_4210_, 1);
v___x_4213_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4214_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4215_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4216_ = lean_string_intercalate(v___x_4215_, v_val_4212_);
v___x_4217_ = lean_string_append(v___x_4214_, v___x_4216_);
lean_dec_ref(v___x_4216_);
v___x_4218_ = lean_box(2);
v___x_4219_ = l_Lean_Syntax_mkNameLit(v___x_4217_, v___x_4218_);
v___x_4220_ = lean_unsigned_to_nat(1u);
v___x_4221_ = lean_mk_empty_array_with_capacity(v___x_4220_);
v___x_4222_ = lean_array_push(v___x_4221_, v___x_4219_);
v___x_4223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4218_);
lean_ctor_set(v___x_4223_, 1, v___x_4213_);
lean_ctor_set(v___x_4223_, 2, v___x_4222_);
return v___x_4223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4224_){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = lean_box(0);
lean_inc(v_n_4224_);
v___x_4226_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4225_, v_n_4224_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_quoteNameMk(v_n_4224_);
return v___x_4227_;
}
else
{
lean_object* v_val_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_dec(v_n_4224_);
v_val_4228_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_val_4228_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4229_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4230_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4231_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4232_ = lean_string_intercalate(v___x_4231_, v_val_4228_);
v___x_4233_ = lean_string_append(v___x_4230_, v___x_4232_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = lean_box(2);
v___x_4235_ = l_Lean_Syntax_mkNameLit(v___x_4233_, v___x_4234_);
v___x_4236_ = lean_unsigned_to_nat(1u);
v___x_4237_ = lean_mk_empty_array_with_capacity(v___x_4236_);
v___x_4238_ = lean_array_push(v___x_4237_, v___x_4235_);
v___x_4239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4234_);
lean_ctor_set(v___x_4239_, 1, v___x_4229_);
lean_ctor_set(v___x_4239_, 2, v___x_4238_);
return v___x_4239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4247_, lean_object* v_inst_4248_, lean_object* v_x_4249_){
_start:
{
lean_object* v_fst_4250_; lean_object* v_snd_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_fst_4250_ = lean_ctor_get(v_x_4249_, 0);
lean_inc(v_fst_4250_);
v_snd_4251_ = lean_ctor_get(v_x_4249_, 1);
lean_inc(v_snd_4251_);
lean_dec_ref(v_x_4249_);
v___x_4252_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4253_ = lean_apply_1(v_inst_4247_, v_fst_4250_);
v___x_4254_ = lean_apply_1(v_inst_4248_, v_snd_4251_);
v___x_4255_ = lean_unsigned_to_nat(2u);
v___x_4256_ = lean_mk_empty_array_with_capacity(v___x_4255_);
v___x_4257_ = lean_array_push(v___x_4256_, v___x_4253_);
v___x_4258_ = lean_array_push(v___x_4257_, v___x_4254_);
v___x_4259_ = l_Lean_Syntax_mkCApp(v___x_4252_, v___x_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4260_, lean_object* v_inst_4261_){
_start:
{
lean_object* v___f_4262_; 
v___f_4262_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4262_, 0, v_inst_4260_);
lean_closure_set(v___f_4262_, 1, v_inst_4261_);
return v___f_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4263_, lean_object* v_00_u03b2_4264_, lean_object* v_inst_4265_, lean_object* v_inst_4266_){
_start:
{
lean_object* v___f_4267_; 
v___f_4267_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4267_, 0, v_inst_4265_);
lean_closure_set(v___f_4267_, 1, v_inst_4266_);
return v___f_4267_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4274_ = l_Lean_mkCIdent(v___x_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4279_, lean_object* v_x_4280_){
_start:
{
if (lean_obj_tag(v_x_4280_) == 0)
{
lean_object* v___x_4281_; 
lean_dec_ref(v_inst_4279_);
v___x_4281_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4281_;
}
else
{
lean_object* v_head_4282_; lean_object* v_tail_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_head_4282_ = lean_ctor_get(v_x_4280_, 0);
lean_inc(v_head_4282_);
v_tail_4283_ = lean_ctor_get(v_x_4280_, 1);
lean_inc(v_tail_4283_);
lean_dec_ref_known(v_x_4280_, 2);
v___x_4284_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4279_);
v___x_4285_ = lean_apply_1(v_inst_4279_, v_head_4282_);
v___x_4286_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4279_, v_tail_4283_);
v___x_4287_ = lean_unsigned_to_nat(2u);
v___x_4288_ = lean_mk_empty_array_with_capacity(v___x_4287_);
v___x_4289_ = lean_array_push(v___x_4288_, v___x_4285_);
v___x_4290_ = lean_array_push(v___x_4289_, v___x_4286_);
v___x_4291_ = l_Lean_Syntax_mkCApp(v___x_4284_, v___x_4290_);
return v___x_4291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4292_, lean_object* v_inst_4293_, lean_object* v_x_4294_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4293_, v_x_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4296_, v_a_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4299_, lean_object* v_inst_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4300_, v_a_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4304_, 0, lean_box(0));
lean_closure_set(v___x_4304_, 1, v_inst_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4305_, lean_object* v_inst_4306_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4307_, 0, lean_box(0));
lean_closure_set(v___x_4307_, 1, v_inst_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4310_, lean_object* v_xs_4311_, lean_object* v_i_4312_, lean_object* v_args_4313_){
_start:
{
lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4314_ = lean_array_get_size(v_xs_4311_);
v___x_4315_ = lean_nat_dec_lt(v_i_4312_, v___x_4314_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec(v_i_4312_);
lean_dec_ref(v_inst_4310_);
v___x_4316_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4317_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4318_ = l_Nat_reprFast(v___x_4314_);
v___x_4319_ = lean_string_append(v___x_4317_, v___x_4318_);
lean_dec_ref(v___x_4318_);
v___x_4320_ = l_Lean_Name_mkStr2(v___x_4316_, v___x_4319_);
v___x_4321_ = l_Lean_Syntax_mkCApp(v___x_4320_, v_args_4313_);
return v___x_4321_;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4322_ = lean_unsigned_to_nat(1u);
v___x_4323_ = lean_nat_add(v_i_4312_, v___x_4322_);
v___x_4324_ = lean_array_fget_borrowed(v_xs_4311_, v_i_4312_);
lean_dec(v_i_4312_);
lean_inc_ref(v_inst_4310_);
lean_inc(v___x_4324_);
v___x_4325_ = lean_apply_1(v_inst_4310_, v___x_4324_);
v___x_4326_ = lean_array_push(v_args_4313_, v___x_4325_);
v_i_4312_ = v___x_4323_;
v_args_4313_ = v___x_4326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4328_, lean_object* v_xs_4329_, lean_object* v_i_4330_, lean_object* v_args_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4328_, v_xs_4329_, v_i_4330_, v_args_4331_);
lean_dec_ref(v_xs_4329_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4333_, lean_object* v_inst_4334_, lean_object* v_xs_4335_, lean_object* v_i_4336_, lean_object* v_args_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4334_, v_xs_4335_, v_i_4336_, v_args_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4339_, lean_object* v_inst_4340_, lean_object* v_xs_4341_, lean_object* v_i_4342_, lean_object* v_args_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4339_, v_inst_4340_, v_xs_4341_, v_i_4342_, v_args_4343_);
lean_dec_ref(v_xs_4341_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4349_, lean_object* v_xs_4350_){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4351_ = lean_array_get_size(v_xs_4350_);
v___x_4352_ = lean_unsigned_to_nat(8u);
v___x_4353_ = lean_nat_dec_le(v___x_4351_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4354_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4355_ = lean_array_to_list(v_xs_4350_);
v___x_4356_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4349_, v___x_4355_);
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = lean_mk_empty_array_with_capacity(v___x_4357_);
v___x_4359_ = lean_array_push(v___x_4358_, v___x_4356_);
v___x_4360_ = l_Lean_Syntax_mkCApp(v___x_4354_, v___x_4359_);
return v___x_4360_;
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4363_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4349_, v_xs_4350_, v___x_4361_, v___x_4362_);
lean_dec_ref(v_xs_4350_);
return v___x_4363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4364_, lean_object* v_inst_4365_, lean_object* v_xs_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4365_, v_xs_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4368_, lean_object* v_xs_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4368_, v_xs_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4371_, lean_object* v_inst_4372_, lean_object* v_xs_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4372_, v_xs_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4375_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4376_, 0, lean_box(0));
lean_closure_set(v___x_4376_, 1, v_inst_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4377_, lean_object* v_inst_4378_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4379_, 0, lean_box(0));
lean_closure_set(v___x_4379_, 1, v_inst_4378_);
return v___x_4379_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4386_ = l_Lean_mkIdent(v___x_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4391_, lean_object* v_x_4392_){
_start:
{
if (lean_obj_tag(v_x_4392_) == 0)
{
lean_object* v___x_4393_; 
lean_dec_ref(v_inst_4391_);
v___x_4393_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4393_;
}
else
{
lean_object* v_val_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_val_4394_ = lean_ctor_get(v_x_4392_, 0);
lean_inc(v_val_4394_);
lean_dec_ref_known(v_x_4392_, 1);
v___x_4395_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4396_ = lean_apply_1(v_inst_4391_, v_val_4394_);
v___x_4397_ = lean_unsigned_to_nat(1u);
v___x_4398_ = lean_mk_empty_array_with_capacity(v___x_4397_);
v___x_4399_ = lean_array_push(v___x_4398_, v___x_4396_);
v___x_4400_ = l_Lean_Syntax_mkCApp(v___x_4395_, v___x_4399_);
return v___x_4400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4401_){
_start:
{
lean_object* v___f_4402_; 
v___f_4402_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4402_, 0, v_inst_4401_);
return v___f_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4403_, lean_object* v_inst_4404_){
_start:
{
lean_object* v___f_4405_; 
v___f_4405_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4405_, 0, v_inst_4404_);
return v___f_4405_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(lean_object* v_k_4406_){
_start:
{
lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4407_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4408_ = lean_name_eq(v_k_4406_, v___x_4407_);
if (v___x_4408_ == 0)
{
uint8_t v___x_4409_; 
v___x_4409_ = 1;
return v___x_4409_;
}
else
{
uint8_t v___x_4410_; 
v___x_4410_ = 0;
return v___x_4410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v_k_4411_){
_start:
{
uint8_t v_res_4412_; lean_object* v_r_4413_; 
v_res_4412_ = l_Lean_evalPrec___lam__0(v_k_4411_);
lean_dec(v_k_4411_);
v_r_4413_ = lean_box(v_res_4412_);
return v_r_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v_methods_4419_; lean_object* v_quotContext_4420_; lean_object* v_currMacroScope_4421_; lean_object* v_currRecDepth_4422_; lean_object* v_maxRecDepth_4423_; lean_object* v_ref_4424_; lean_object* v___f_4425_; lean_object* v_methods_4427_; lean_object* v_quotContext_4428_; lean_object* v_currMacroScope_4429_; lean_object* v_currRecDepth_4430_; lean_object* v_maxRecDepth_4431_; lean_object* v_ref_4432_; lean_object* v___y_4433_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v_methods_4419_ = lean_ctor_get(v_a_4417_, 0);
v_quotContext_4420_ = lean_ctor_get(v_a_4417_, 1);
v_currMacroScope_4421_ = lean_ctor_get(v_a_4417_, 2);
v_currRecDepth_4422_ = lean_ctor_get(v_a_4417_, 3);
v_maxRecDepth_4423_ = lean_ctor_get(v_a_4417_, 4);
v_ref_4424_ = lean_ctor_get(v_a_4417_, 5);
v___f_4425_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = lean_nat_dec_eq(v_maxRecDepth_4423_, v___x_4461_);
if (v___x_4462_ == 0)
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_nat_dec_eq(v_currRecDepth_4422_, v_maxRecDepth_4423_);
if (v___x_4463_ == 0)
{
v_methods_4427_ = v_methods_4419_;
v_quotContext_4428_ = v_quotContext_4420_;
v_currMacroScope_4429_ = v_currMacroScope_4421_;
v_currRecDepth_4430_ = v_currRecDepth_4422_;
v_maxRecDepth_4431_ = v_maxRecDepth_4423_;
v_ref_4432_ = v_ref_4424_;
v___y_4433_ = v_a_4418_;
goto v___jp_4426_;
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4464_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4465_, 0, v_stx_4416_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
v___x_4466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
lean_ctor_set(v___x_4466_, 1, v_a_4418_);
return v___x_4466_;
}
}
else
{
v_methods_4427_ = v_methods_4419_;
v_quotContext_4428_ = v_quotContext_4420_;
v_currMacroScope_4429_ = v_currMacroScope_4421_;
v_currRecDepth_4430_ = v_currRecDepth_4422_;
v_maxRecDepth_4431_ = v_maxRecDepth_4423_;
v_ref_4432_ = v_ref_4424_;
v___y_4433_ = v_a_4418_;
goto v___jp_4426_;
}
v___jp_4426_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4434_ = lean_unsigned_to_nat(1u);
v___x_4435_ = lean_nat_add(v_currRecDepth_4430_, v___x_4434_);
lean_inc(v_ref_4432_);
lean_inc(v_maxRecDepth_4431_);
lean_inc(v_currMacroScope_4429_);
lean_inc(v_quotContext_4428_);
lean_inc(v_methods_4427_);
v___x_4436_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4436_, 0, v_methods_4427_);
lean_ctor_set(v___x_4436_, 1, v_quotContext_4428_);
lean_ctor_set(v___x_4436_, 2, v_currMacroScope_4429_);
lean_ctor_set(v___x_4436_, 3, v___x_4435_);
lean_ctor_set(v___x_4436_, 4, v_maxRecDepth_4431_);
lean_ctor_set(v___x_4436_, 5, v_ref_4432_);
lean_inc_ref(v___x_4436_);
v___x_4437_ = l_Lean_expandMacros(v_stx_4416_, v___f_4425_, v___x_4436_, v___y_4433_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4451_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_a_4439_ = lean_ctor_get(v___x_4437_, 1);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4441_ = v___x_4437_;
v_isShared_4442_ = v_isSharedCheck_4451_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4451_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; uint8_t v___x_4444_; 
v___x_4443_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4438_);
v___x_4444_ = l_Lean_Syntax_isOfKind(v_a_4438_, v___x_4443_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
lean_del_object(v___x_4441_);
v___x_4445_ = ((lean_object*)(l_Lean_evalPrec___closed__1));
v___x_4446_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4438_, v___x_4445_, v___x_4436_, v_a_4439_);
lean_dec_ref_known(v___x_4436_, 6);
lean_dec(v_a_4438_);
return v___x_4446_;
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
lean_dec_ref_known(v___x_4436_, 6);
v___x_4447_ = l_Lean_TSyntax_getNat(v_a_4438_);
lean_dec(v_a_4438_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4447_);
v___x_4449_ = v___x_4441_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_a_4439_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec_ref_known(v___x_4436_, 6);
v_a_4452_ = lean_ctor_get(v___x_4437_, 0);
v_a_4453_ = lean_ctor_get(v___x_4437_, 1);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4437_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_inc(v_a_4452_);
lean_dec(v___x_4437_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4452_);
lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Lean_evalPrec(v_stx_4467_, v_a_4468_, v_a_4469_);
lean_dec_ref(v_a_4468_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_methods_4475_; lean_object* v_quotContext_4476_; lean_object* v_currMacroScope_4477_; lean_object* v_currRecDepth_4478_; lean_object* v_maxRecDepth_4479_; lean_object* v_ref_4480_; lean_object* v___f_4481_; lean_object* v_methods_4483_; lean_object* v_quotContext_4484_; lean_object* v_currMacroScope_4485_; lean_object* v_currRecDepth_4486_; lean_object* v_maxRecDepth_4487_; lean_object* v_ref_4488_; lean_object* v___y_4489_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v_methods_4475_ = lean_ctor_get(v_a_4473_, 0);
v_quotContext_4476_ = lean_ctor_get(v_a_4473_, 1);
v_currMacroScope_4477_ = lean_ctor_get(v_a_4473_, 2);
v_currRecDepth_4478_ = lean_ctor_get(v_a_4473_, 3);
v_maxRecDepth_4479_ = lean_ctor_get(v_a_4473_, 4);
v_ref_4480_ = lean_ctor_get(v_a_4473_, 5);
v___f_4481_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = lean_nat_dec_eq(v_maxRecDepth_4479_, v___x_4517_);
if (v___x_4518_ == 0)
{
uint8_t v___x_4519_; 
v___x_4519_ = lean_nat_dec_eq(v_currRecDepth_4478_, v_maxRecDepth_4479_);
if (v___x_4519_ == 0)
{
v_methods_4483_ = v_methods_4475_;
v_quotContext_4484_ = v_quotContext_4476_;
v_currMacroScope_4485_ = v_currMacroScope_4477_;
v_currRecDepth_4486_ = v_currRecDepth_4478_;
v_maxRecDepth_4487_ = v_maxRecDepth_4479_;
v_ref_4488_ = v_ref_4480_;
v___y_4489_ = v_a_4474_;
goto v___jp_4482_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4521_, 0, v_stx_4472_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
v___x_4522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v_a_4474_);
return v___x_4522_;
}
}
else
{
v_methods_4483_ = v_methods_4475_;
v_quotContext_4484_ = v_quotContext_4476_;
v_currMacroScope_4485_ = v_currMacroScope_4477_;
v_currRecDepth_4486_ = v_currRecDepth_4478_;
v_maxRecDepth_4487_ = v_maxRecDepth_4479_;
v_ref_4488_ = v_ref_4480_;
v___y_4489_ = v_a_4474_;
goto v___jp_4482_;
}
v___jp_4482_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4490_ = lean_unsigned_to_nat(1u);
v___x_4491_ = lean_nat_add(v_currRecDepth_4486_, v___x_4490_);
lean_inc(v_ref_4488_);
lean_inc(v_maxRecDepth_4487_);
lean_inc(v_currMacroScope_4485_);
lean_inc(v_quotContext_4484_);
lean_inc(v_methods_4483_);
v___x_4492_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4492_, 0, v_methods_4483_);
lean_ctor_set(v___x_4492_, 1, v_quotContext_4484_);
lean_ctor_set(v___x_4492_, 2, v_currMacroScope_4485_);
lean_ctor_set(v___x_4492_, 3, v___x_4491_);
lean_ctor_set(v___x_4492_, 4, v_maxRecDepth_4487_);
lean_ctor_set(v___x_4492_, 5, v_ref_4488_);
lean_inc_ref(v___x_4492_);
v___x_4493_ = l_Lean_expandMacros(v_stx_4472_, v___f_4481_, v___x_4492_, v___y_4489_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4507_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
v_a_4495_ = lean_ctor_get(v___x_4493_, 1);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4497_ = v___x_4493_;
v_isShared_4498_ = v_isSharedCheck_4507_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_inc(v_a_4494_);
lean_dec(v___x_4493_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4507_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4499_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4494_);
v___x_4500_ = l_Lean_Syntax_isOfKind(v_a_4494_, v___x_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
lean_del_object(v___x_4497_);
v___x_4501_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4502_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4494_, v___x_4501_, v___x_4492_, v_a_4495_);
lean_dec_ref_known(v___x_4492_, 6);
lean_dec(v_a_4494_);
return v___x_4502_;
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
lean_dec_ref_known(v___x_4492_, 6);
v___x_4503_ = l_Lean_TSyntax_getNat(v_a_4494_);
lean_dec(v_a_4494_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4503_);
v___x_4505_ = v___x_4497_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_a_4495_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec_ref_known(v___x_4492_, 6);
v_a_4508_ = lean_ctor_get(v___x_4493_, 0);
v_a_4509_ = lean_ctor_get(v___x_4493_, 1);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4493_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_inc(v_a_4508_);
lean_dec(v___x_4493_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4508_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_evalPrio(v_stx_4523_, v_a_4524_, v_a_4525_);
lean_dec_ref(v_a_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
if (lean_obj_tag(v_x_4527_) == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = lean_unsigned_to_nat(1000u);
v___x_4531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
lean_ctor_set(v___x_4531_, 1, v_a_4529_);
return v___x_4531_;
}
else
{
lean_object* v_val_4532_; lean_object* v___x_4533_; 
v_val_4532_ = lean_ctor_get(v_x_4527_, 0);
lean_inc(v_val_4532_);
lean_dec_ref_known(v_x_4527_, 1);
v___x_4533_ = l_Lean_evalPrio(v_val_4532_, v_a_4528_, v_a_4529_);
return v___x_4533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_evalOptPrio(v_x_4534_, v_a_4535_, v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4538_, lean_object* v_x1_4539_, lean_object* v_x2_4540_){
_start:
{
lean_object* v_fst_4541_; uint8_t v___x_4542_; 
v_fst_4541_ = lean_ctor_get(v_x1_4539_, 0);
v___x_4542_ = lean_unbox(v_fst_4541_);
if (v___x_4542_ == 0)
{
lean_object* v_snd_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_x2_4540_);
v_snd_4543_ = lean_ctor_get(v_x1_4539_, 1);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_x1_4539_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v_x1_4539_, 0);
lean_dec(v_unused_4552_);
v___x_4545_ = v_x1_4539_;
v_isShared_4546_ = v_isSharedCheck_4551_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_snd_4543_);
lean_dec(v_x1_4539_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4551_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4547_; lean_object* v___x_4549_; 
v___x_4547_ = lean_box(v___x_4538_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4547_);
v___x_4549_ = v___x_4545_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_snd_4543_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
else
{
lean_object* v_snd_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4563_; 
v_snd_4553_ = lean_ctor_get(v_x1_4539_, 1);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_x1_4539_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; 
v_unused_4564_ = lean_ctor_get(v_x1_4539_, 0);
lean_dec(v_unused_4564_);
v___x_4555_ = v_x1_4539_;
v_isShared_4556_ = v_isSharedCheck_4563_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_snd_4553_);
lean_dec(v_x1_4539_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4563_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
uint8_t v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4561_; 
v___x_4557_ = 0;
v___x_4558_ = lean_array_push(v_snd_4553_, v_x2_4540_);
v___x_4559_ = lean_box(v___x_4557_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 1, v___x_4558_);
lean_ctor_set(v___x_4555_, 0, v___x_4559_);
v___x_4561_ = v___x_4555_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v___x_4558_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4565_, lean_object* v_x1_4566_, lean_object* v_x2_4567_){
_start:
{
uint8_t v___x_87__boxed_4568_; lean_object* v_res_4569_; 
v___x_87__boxed_4568_ = lean_unbox(v___x_4565_);
v_res_4569_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4568_, v_x1_4566_, v_x2_4567_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4591_){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v___x_4592_ = lean_unsigned_to_nat(0u);
v___x_4593_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4594_ = lean_array_get_size(v_as_4591_);
v___x_4595_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4596_ = lean_nat_dec_lt(v___x_4592_, v___x_4594_);
if (v___x_4596_ == 0)
{
lean_dec_ref(v_as_4591_);
return v___x_4593_;
}
else
{
lean_object* v___x_4597_; lean_object* v___f_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; size_t v___x_4601_; size_t v___x_4602_; lean_object* v___x_4603_; lean_object* v_snd_4604_; 
v___x_4597_ = lean_box(v___x_4596_);
v___f_4598_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4598_, 0, v___x_4597_);
v___x_4599_ = lean_box(v___x_4596_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
lean_ctor_set(v___x_4600_, 1, v___x_4593_);
v___x_4601_ = ((size_t)0ULL);
v___x_4602_ = lean_usize_of_nat(v___x_4594_);
v___x_4603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4595_, v___f_4598_, v_as_4591_, v___x_4601_, v___x_4602_, v___x_4600_);
v_snd_4604_ = lean_ctor_get(v___x_4603_, 1);
lean_inc(v_snd_4604_);
lean_dec(v___x_4603_);
return v_snd_4604_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4605_, lean_object* v_as_4606_){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; 
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4609_ = lean_array_get_size(v_as_4606_);
v___x_4610_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4611_ = lean_nat_dec_lt(v___x_4607_, v___x_4609_);
if (v___x_4611_ == 0)
{
lean_dec_ref(v_as_4606_);
return v___x_4608_;
}
else
{
lean_object* v___x_4612_; lean_object* v___f_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; size_t v___x_4616_; size_t v___x_4617_; lean_object* v___x_4618_; lean_object* v_snd_4619_; 
v___x_4612_ = lean_box(v___x_4611_);
v___f_4613_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4613_, 0, v___x_4612_);
v___x_4614_ = lean_box(v___x_4611_);
v___x_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
lean_ctor_set(v___x_4615_, 1, v___x_4608_);
v___x_4616_ = ((size_t)0ULL);
v___x_4617_ = lean_usize_of_nat(v___x_4609_);
v___x_4618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4610_, v___f_4613_, v_as_4606_, v___x_4616_, v___x_4617_, v___x_4615_);
v_snd_4619_ = lean_ctor_get(v___x_4618_, 1);
lean_inc(v_snd_4619_);
lean_dec(v___x_4618_);
return v_snd_4619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4620_, lean_object* v_inst_4621_, lean_object* v_a_4622_, lean_object* v_p_4623_, lean_object* v_acc_4624_, lean_object* v_stx_4625_, uint8_t v_____do__lift_4626_){
_start:
{
if (v_____do__lift_4626_ == 0)
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_dec(v_stx_4625_);
v___x_4627_ = lean_unsigned_to_nat(2u);
v___x_4628_ = lean_nat_add(v_i_4620_, v___x_4627_);
v___x_4629_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4621_, v_a_4622_, v_p_4623_, v___x_4628_, v_acc_4624_);
return v___x_4629_;
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4630_ = lean_array_get_size(v_acc_4624_);
v___x_4631_ = lean_unsigned_to_nat(0u);
v___x_4632_ = lean_nat_dec_eq(v___x_4630_, v___x_4631_);
if (v___x_4632_ == 0)
{
uint8_t v___x_4633_; 
v___x_4633_ = lean_nat_dec_eq(v_i_4620_, v___x_4631_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; lean_object* v_sepStx_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4634_ = lean_nat_pred(v_i_4620_);
v_sepStx_4635_ = lean_array_fget_borrowed(v_a_4622_, v___x_4634_);
lean_dec(v___x_4634_);
v___x_4636_ = lean_unsigned_to_nat(2u);
v___x_4637_ = lean_nat_add(v_i_4620_, v___x_4636_);
lean_inc(v_sepStx_4635_);
v___x_4638_ = lean_array_push(v_acc_4624_, v_sepStx_4635_);
v___x_4639_ = lean_array_push(v___x_4638_, v_stx_4625_);
v___x_4640_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4621_, v_a_4622_, v_p_4623_, v___x_4637_, v___x_4639_);
return v___x_4640_;
}
else
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = lean_unsigned_to_nat(2u);
v___x_4642_ = lean_nat_add(v_i_4620_, v___x_4641_);
v___x_4643_ = lean_array_push(v_acc_4624_, v_stx_4625_);
v___x_4644_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4621_, v_a_4622_, v_p_4623_, v___x_4642_, v___x_4643_);
return v___x_4644_;
}
}
else
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4645_ = lean_unsigned_to_nat(2u);
v___x_4646_ = lean_nat_add(v_i_4620_, v___x_4645_);
v___x_4647_ = lean_array_push(v_acc_4624_, v_stx_4625_);
v___x_4648_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4621_, v_a_4622_, v_p_4623_, v___x_4646_, v___x_4647_);
return v___x_4648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4649_, lean_object* v_inst_4650_, lean_object* v_a_4651_, lean_object* v_p_4652_, lean_object* v_acc_4653_, lean_object* v_stx_4654_, lean_object* v_____do__lift_4655_){
_start:
{
uint8_t v_____do__lift_218__boxed_4656_; lean_object* v_res_4657_; 
v_____do__lift_218__boxed_4656_ = lean_unbox(v_____do__lift_4655_);
v_res_4657_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4649_, v_inst_4650_, v_a_4651_, v_p_4652_, v_acc_4653_, v_stx_4654_, v_____do__lift_218__boxed_4656_);
lean_dec(v_i_4649_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4658_, lean_object* v_a_4659_, lean_object* v_p_4660_, lean_object* v_i_4661_, lean_object* v_acc_4662_){
_start:
{
lean_object* v_toApplicative_4663_; lean_object* v_toBind_4664_; lean_object* v_toPure_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v_toApplicative_4663_ = lean_ctor_get(v_inst_4658_, 0);
v_toBind_4664_ = lean_ctor_get(v_inst_4658_, 1);
lean_inc(v_toBind_4664_);
v_toPure_4665_ = lean_ctor_get(v_toApplicative_4663_, 1);
v___x_4666_ = lean_array_get_size(v_a_4659_);
v___x_4667_ = lean_nat_dec_lt(v_i_4661_, v___x_4666_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; 
lean_inc(v_toPure_4665_);
lean_dec(v_toBind_4664_);
lean_dec(v_i_4661_);
lean_dec(v_p_4660_);
lean_dec_ref(v_a_4659_);
lean_dec_ref(v_inst_4658_);
v___x_4668_ = lean_apply_2(v_toPure_4665_, lean_box(0), v_acc_4662_);
return v___x_4668_;
}
else
{
lean_object* v_stx_4669_; lean_object* v___f_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v_stx_4669_ = lean_array_fget(v_a_4659_, v_i_4661_);
lean_inc(v_stx_4669_);
lean_inc(v_p_4660_);
v___f_4670_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4670_, 0, v_i_4661_);
lean_closure_set(v___f_4670_, 1, v_inst_4658_);
lean_closure_set(v___f_4670_, 2, v_a_4659_);
lean_closure_set(v___f_4670_, 3, v_p_4660_);
lean_closure_set(v___f_4670_, 4, v_acc_4662_);
lean_closure_set(v___f_4670_, 5, v_stx_4669_);
v___x_4671_ = lean_apply_1(v_p_4660_, v_stx_4669_);
v___x_4672_ = lean_apply_4(v_toBind_4664_, lean_box(0), lean_box(0), v___x_4671_, v___f_4670_);
return v___x_4672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4673_, lean_object* v_inst_4674_, lean_object* v_a_4675_, lean_object* v_p_4676_, lean_object* v_i_4677_, lean_object* v_acc_4678_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4674_, v_a_4675_, v_p_4676_, v_i_4677_, v_acc_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4680_, lean_object* v_a_4681_, lean_object* v_p_4682_){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4683_ = lean_unsigned_to_nat(0u);
v___x_4684_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4685_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4680_, v_a_4681_, v_p_4682_, v___x_4683_, v___x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4686_, lean_object* v_inst_4687_, lean_object* v_a_4688_, lean_object* v_p_4689_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Array_filterSepElemsM___redArg(v_inst_4687_, v_a_4688_, v_p_4689_);
return v___x_4690_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4691_, lean_object* v_x_4692_){
_start:
{
lean_object* v___x_4693_; uint8_t v___x_4694_; 
v___x_4693_ = lean_apply_1(v_p_4691_, v_x_4692_);
v___x_4694_ = lean_unbox(v___x_4693_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4695_, lean_object* v_x_4696_){
_start:
{
uint8_t v_res_4697_; lean_object* v_r_4698_; 
v_res_4697_ = l_Array_filterSepElems___lam__0(v_p_4695_, v_x_4696_);
v_r_4698_ = lean_box(v_res_4697_);
return v_r_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4699_, lean_object* v_p_4700_, lean_object* v_i_4701_, lean_object* v_acc_4702_){
_start:
{
lean_object* v___x_4703_; uint8_t v___x_4704_; 
v___x_4703_ = lean_array_get_size(v_a_4699_);
v___x_4704_ = lean_nat_dec_lt(v_i_4701_, v___x_4703_);
if (v___x_4704_ == 0)
{
lean_dec(v_i_4701_);
lean_dec_ref(v_p_4700_);
return v_acc_4702_;
}
else
{
lean_object* v_stx_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; 
v_stx_4705_ = lean_array_fget_borrowed(v_a_4699_, v_i_4701_);
lean_inc_ref(v_p_4700_);
lean_inc(v_stx_4705_);
v___x_4706_ = lean_apply_1(v_p_4700_, v_stx_4705_);
v___x_4707_ = lean_unbox(v___x_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4708_ = lean_unsigned_to_nat(2u);
v___x_4709_ = lean_nat_add(v_i_4701_, v___x_4708_);
lean_dec(v_i_4701_);
v_i_4701_ = v___x_4709_;
goto _start;
}
else
{
lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4711_ = lean_array_get_size(v_acc_4702_);
v___x_4712_ = lean_unsigned_to_nat(0u);
v___x_4713_ = lean_nat_dec_eq(v___x_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
uint8_t v___x_4714_; 
v___x_4714_ = lean_nat_dec_eq(v_i_4701_, v___x_4712_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; lean_object* v_sepStx_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4715_ = lean_nat_pred(v_i_4701_);
v_sepStx_4716_ = lean_array_fget_borrowed(v_a_4699_, v___x_4715_);
lean_dec(v___x_4715_);
v___x_4717_ = lean_unsigned_to_nat(2u);
v___x_4718_ = lean_nat_add(v_i_4701_, v___x_4717_);
lean_dec(v_i_4701_);
lean_inc(v_sepStx_4716_);
v___x_4719_ = lean_array_push(v_acc_4702_, v_sepStx_4716_);
lean_inc(v_stx_4705_);
v___x_4720_ = lean_array_push(v___x_4719_, v_stx_4705_);
v_i_4701_ = v___x_4718_;
v_acc_4702_ = v___x_4720_;
goto _start;
}
else
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4722_ = lean_unsigned_to_nat(2u);
v___x_4723_ = lean_nat_add(v_i_4701_, v___x_4722_);
lean_dec(v_i_4701_);
lean_inc(v_stx_4705_);
v___x_4724_ = lean_array_push(v_acc_4702_, v_stx_4705_);
v_i_4701_ = v___x_4723_;
v_acc_4702_ = v___x_4724_;
goto _start;
}
}
else
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = lean_unsigned_to_nat(2u);
v___x_4727_ = lean_nat_add(v_i_4701_, v___x_4726_);
lean_dec(v_i_4701_);
lean_inc(v_stx_4705_);
v___x_4728_ = lean_array_push(v_acc_4702_, v_stx_4705_);
v_i_4701_ = v___x_4727_;
v_acc_4702_ = v___x_4728_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4730_, lean_object* v_p_4731_, lean_object* v_i_4732_, lean_object* v_acc_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4730_, v_p_4731_, v_i_4732_, v_acc_4733_);
lean_dec_ref(v_a_4730_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4735_, lean_object* v_p_4736_){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = lean_unsigned_to_nat(0u);
v___x_4738_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4739_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4735_, v_p_4736_, v___x_4737_, v___x_4738_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4740_, lean_object* v_p_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4740_, v_p_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4743_, lean_object* v_p_4744_){
_start:
{
lean_object* v___f_4745_; lean_object* v___x_4746_; 
v___f_4745_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4745_, 0, v_p_4744_);
v___x_4746_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4743_, v___f_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4747_, lean_object* v_p_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_Array_filterSepElems(v_a_4747_, v_p_4748_);
lean_dec_ref(v_a_4747_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4750_, lean_object* v_acc_4751_, lean_object* v_inst_4752_, lean_object* v_a_4753_, lean_object* v_f_4754_, lean_object* v_stx_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4750_, v_acc_4751_, v_inst_4752_, v_a_4753_, v_f_4754_, v_stx_4755_);
lean_dec(v_i_4750_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4757_, lean_object* v_a_4758_, lean_object* v_f_4759_, lean_object* v_i_4760_, lean_object* v_acc_4761_){
_start:
{
lean_object* v_toApplicative_4762_; lean_object* v_toBind_4763_; lean_object* v_toPure_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v_toApplicative_4762_ = lean_ctor_get(v_inst_4757_, 0);
v_toBind_4763_ = lean_ctor_get(v_inst_4757_, 1);
v_toPure_4764_ = lean_ctor_get(v_toApplicative_4762_, 1);
v___x_4765_ = lean_array_get_size(v_a_4758_);
v___x_4766_ = lean_nat_dec_lt(v_i_4760_, v___x_4765_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; 
lean_inc(v_toPure_4764_);
lean_dec(v_i_4760_);
lean_dec(v_f_4759_);
lean_dec_ref(v_a_4758_);
lean_dec_ref(v_inst_4757_);
v___x_4767_ = lean_apply_2(v_toPure_4764_, lean_box(0), v_acc_4761_);
return v___x_4767_;
}
else
{
lean_object* v_stx_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
v_stx_4768_ = lean_array_fget_borrowed(v_a_4758_, v_i_4760_);
v___x_4769_ = lean_unsigned_to_nat(2u);
v___x_4770_ = lean_nat_mod(v_i_4760_, v___x_4769_);
v___x_4771_ = lean_unsigned_to_nat(0u);
v___x_4772_ = lean_nat_dec_eq(v___x_4770_, v___x_4771_);
lean_dec(v___x_4770_);
if (v___x_4772_ == 0)
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4773_ = lean_unsigned_to_nat(1u);
v___x_4774_ = lean_nat_add(v_i_4760_, v___x_4773_);
lean_dec(v_i_4760_);
lean_inc(v_stx_4768_);
v___x_4775_ = lean_array_push(v_acc_4761_, v_stx_4768_);
v_i_4760_ = v___x_4774_;
v_acc_4761_ = v___x_4775_;
goto _start;
}
else
{
lean_object* v___f_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
lean_inc(v_stx_4768_);
lean_inc(v_toBind_4763_);
lean_inc(v_f_4759_);
v___f_4777_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4777_, 0, v_i_4760_);
lean_closure_set(v___f_4777_, 1, v_acc_4761_);
lean_closure_set(v___f_4777_, 2, v_inst_4757_);
lean_closure_set(v___f_4777_, 3, v_a_4758_);
lean_closure_set(v___f_4777_, 4, v_f_4759_);
v___x_4778_ = lean_apply_1(v_f_4759_, v_stx_4768_);
v___x_4779_ = lean_apply_4(v_toBind_4763_, lean_box(0), lean_box(0), v___x_4778_, v___f_4777_);
return v___x_4779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4780_, lean_object* v_acc_4781_, lean_object* v_inst_4782_, lean_object* v_a_4783_, lean_object* v_f_4784_, lean_object* v_stx_4785_){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4786_ = lean_unsigned_to_nat(1u);
v___x_4787_ = lean_nat_add(v_i_4780_, v___x_4786_);
v___x_4788_ = lean_array_push(v_acc_4781_, v_stx_4785_);
v___x_4789_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4782_, v_a_4783_, v_f_4784_, v___x_4787_, v___x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4790_, lean_object* v_inst_4791_, lean_object* v_a_4792_, lean_object* v_f_4793_, lean_object* v_i_4794_, lean_object* v_acc_4795_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4791_, v_a_4792_, v_f_4793_, v_i_4794_, v_acc_4795_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4797_, lean_object* v_a_4798_, lean_object* v_f_4799_){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4800_ = lean_unsigned_to_nat(0u);
v___x_4801_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4802_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4797_, v_a_4798_, v_f_4799_, v___x_4800_, v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4803_, lean_object* v_inst_4804_, lean_object* v_a_4805_, lean_object* v_f_4806_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l_Array_mapSepElemsM___redArg(v_inst_4804_, v_a_4805_, v_f_4806_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4808_, lean_object* v_x_4809_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = lean_apply_1(v_f_4808_, v_x_4809_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4811_, lean_object* v_f_4812_, lean_object* v_i_4813_, lean_object* v_acc_4814_){
_start:
{
lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4815_ = lean_array_get_size(v_a_4811_);
v___x_4816_ = lean_nat_dec_lt(v_i_4813_, v___x_4815_);
if (v___x_4816_ == 0)
{
lean_dec(v_i_4813_);
lean_dec_ref(v_f_4812_);
return v_acc_4814_;
}
else
{
lean_object* v_stx_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; 
v_stx_4817_ = lean_array_fget_borrowed(v_a_4811_, v_i_4813_);
v___x_4818_ = lean_unsigned_to_nat(2u);
v___x_4819_ = lean_nat_mod(v_i_4813_, v___x_4818_);
v___x_4820_ = lean_unsigned_to_nat(0u);
v___x_4821_ = lean_nat_dec_eq(v___x_4819_, v___x_4820_);
lean_dec(v___x_4819_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4822_ = lean_unsigned_to_nat(1u);
v___x_4823_ = lean_nat_add(v_i_4813_, v___x_4822_);
lean_dec(v_i_4813_);
lean_inc(v_stx_4817_);
v___x_4824_ = lean_array_push(v_acc_4814_, v_stx_4817_);
v_i_4813_ = v___x_4823_;
v_acc_4814_ = v___x_4824_;
goto _start;
}
else
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_inc_ref(v_f_4812_);
lean_inc(v_stx_4817_);
v___x_4826_ = lean_apply_1(v_f_4812_, v_stx_4817_);
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4828_ = lean_nat_add(v_i_4813_, v___x_4827_);
lean_dec(v_i_4813_);
v___x_4829_ = lean_array_push(v_acc_4814_, v___x_4826_);
v_i_4813_ = v___x_4828_;
v_acc_4814_ = v___x_4829_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4831_, lean_object* v_f_4832_, lean_object* v_i_4833_, lean_object* v_acc_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4831_, v_f_4832_, v_i_4833_, v_acc_4834_);
lean_dec_ref(v_a_4831_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4836_, lean_object* v_f_4837_){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = lean_unsigned_to_nat(0u);
v___x_4839_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4840_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4836_, v_f_4837_, v___x_4838_, v___x_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4841_, lean_object* v_f_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4841_, v_f_4842_);
lean_dec_ref(v_a_4841_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4844_, lean_object* v_f_4845_){
_start:
{
lean_object* v___f_4846_; lean_object* v___x_4847_; 
v___f_4846_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4846_, 0, v_f_4845_);
v___x_4847_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4844_, v___f_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4848_, lean_object* v_f_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Array_mapSepElems(v_a_4848_, v_f_4849_);
lean_dec_ref(v_a_4848_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4851_, size_t v_i_4852_, size_t v_stop_4853_, lean_object* v_b_4854_){
_start:
{
lean_object* v___y_4856_; uint8_t v___x_4860_; 
v___x_4860_ = lean_usize_dec_eq(v_i_4852_, v_stop_4853_);
if (v___x_4860_ == 0)
{
lean_object* v_fst_4861_; uint8_t v___x_4862_; 
v_fst_4861_ = lean_ctor_get(v_b_4854_, 0);
v___x_4862_ = lean_unbox(v_fst_4861_);
if (v___x_4862_ == 0)
{
lean_object* v_snd_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4872_; 
v_snd_4863_ = lean_ctor_get(v_b_4854_, 1);
v_isSharedCheck_4872_ = !lean_is_exclusive(v_b_4854_);
if (v_isSharedCheck_4872_ == 0)
{
lean_object* v_unused_4873_; 
v_unused_4873_ = lean_ctor_get(v_b_4854_, 0);
lean_dec(v_unused_4873_);
v___x_4865_ = v_b_4854_;
v_isShared_4866_ = v_isSharedCheck_4872_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_snd_4863_);
lean_dec(v_b_4854_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4872_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4870_; 
v___x_4867_ = 1;
v___x_4868_ = lean_box(v___x_4867_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 0, v___x_4868_);
v___x_4870_ = v___x_4865_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4868_);
lean_ctor_set(v_reuseFailAlloc_4871_, 1, v_snd_4863_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
v___y_4856_ = v___x_4870_;
goto v___jp_4855_;
}
}
}
else
{
lean_object* v_snd_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4884_; 
v_snd_4874_ = lean_ctor_get(v_b_4854_, 1);
v_isSharedCheck_4884_ = !lean_is_exclusive(v_b_4854_);
if (v_isSharedCheck_4884_ == 0)
{
lean_object* v_unused_4885_; 
v_unused_4885_ = lean_ctor_get(v_b_4854_, 0);
lean_dec(v_unused_4885_);
v___x_4876_ = v_b_4854_;
v_isShared_4877_ = v_isSharedCheck_4884_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_snd_4874_);
lean_dec(v_b_4854_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4884_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4878_ = lean_array_uget_borrowed(v_as_4851_, v_i_4852_);
lean_inc(v___x_4878_);
v___x_4879_ = lean_array_push(v_snd_4874_, v___x_4878_);
v___x_4880_ = lean_box(v___x_4860_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 1, v___x_4879_);
lean_ctor_set(v___x_4876_, 0, v___x_4880_);
v___x_4882_ = v___x_4876_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
lean_ctor_set(v_reuseFailAlloc_4883_, 1, v___x_4879_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
v___y_4856_ = v___x_4882_;
goto v___jp_4855_;
}
}
}
}
else
{
return v_b_4854_;
}
v___jp_4855_:
{
size_t v___x_4857_; size_t v___x_4858_; 
v___x_4857_ = ((size_t)1ULL);
v___x_4858_ = lean_usize_add(v_i_4852_, v___x_4857_);
v_i_4852_ = v___x_4858_;
v_b_4854_ = v___y_4856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4886_, lean_object* v_i_4887_, lean_object* v_stop_4888_, lean_object* v_b_4889_){
_start:
{
size_t v_i_boxed_4890_; size_t v_stop_boxed_4891_; lean_object* v_res_4892_; 
v_i_boxed_4890_ = lean_unbox_usize(v_i_4887_);
lean_dec(v_i_4887_);
v_stop_boxed_4891_ = lean_unbox_usize(v_stop_4888_);
lean_dec(v_stop_4888_);
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4886_, v_i_boxed_4890_, v_stop_boxed_4891_, v_b_4889_);
lean_dec_ref(v_as_4886_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4893_){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; uint8_t v___x_4897_; 
v___x_4894_ = lean_unsigned_to_nat(0u);
v___x_4895_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4896_ = lean_array_get_size(v_sa_4893_);
v___x_4897_ = lean_nat_dec_lt(v___x_4894_, v___x_4896_);
if (v___x_4897_ == 0)
{
return v___x_4895_;
}
else
{
lean_object* v___x_4898_; lean_object* v___x_4899_; size_t v___x_4900_; size_t v___x_4901_; lean_object* v___x_4902_; lean_object* v_snd_4903_; 
v___x_4898_ = lean_box(v___x_4897_);
v___x_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
lean_ctor_set(v___x_4899_, 1, v___x_4895_);
v___x_4900_ = ((size_t)0ULL);
v___x_4901_ = lean_usize_of_nat(v___x_4896_);
v___x_4902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4893_, v___x_4900_, v___x_4901_, v___x_4899_);
v_snd_4903_ = lean_ctor_get(v___x_4902_, 1);
lean_inc(v_snd_4903_);
lean_dec_ref(v___x_4902_);
return v_snd_4903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4904_);
lean_dec_ref(v_sa_4904_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4906_, lean_object* v_sa_4907_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4907_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4909_, lean_object* v_sa_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Syntax_SepArray_getElems(v_sep_4909_, v_sa_4910_);
lean_dec_ref(v_sa_4910_);
lean_dec_ref(v_sep_4909_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4912_){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; uint8_t v___x_4916_; 
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4915_ = lean_array_get_size(v_sa_4912_);
v___x_4916_ = lean_nat_dec_lt(v___x_4913_, v___x_4915_);
if (v___x_4916_ == 0)
{
return v___x_4914_;
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4918_; size_t v___x_4919_; size_t v___x_4920_; lean_object* v___x_4921_; lean_object* v_snd_4922_; 
v___x_4917_ = lean_box(v___x_4916_);
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v___x_4914_);
v___x_4919_ = ((size_t)0ULL);
v___x_4920_ = lean_usize_of_nat(v___x_4915_);
v___x_4921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4912_, v___x_4919_, v___x_4920_, v___x_4918_);
v_snd_4922_ = lean_ctor_get(v___x_4921_, 1);
lean_inc(v_snd_4922_);
lean_dec_ref(v___x_4921_);
return v_snd_4922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4923_);
lean_dec_ref(v_sa_4923_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4925_, lean_object* v_sep_4926_, lean_object* v_sa_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4929_, lean_object* v_sep_4930_, lean_object* v_sa_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_Syntax_TSepArray_getElems(v_k_4929_, v_sep_4930_, v_sa_4931_);
lean_dec_ref(v_sa_4931_);
lean_dec_ref(v_sep_4930_);
lean_dec(v_k_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4933_, lean_object* v_sa_4934_, lean_object* v_e_4935_){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4936_ = lean_array_get_size(v_sa_4934_);
v___x_4937_ = lean_unsigned_to_nat(0u);
v___x_4938_ = lean_nat_dec_eq(v___x_4936_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4939_ = l_Lean_mkAtom(v_sep_4933_);
v___x_4940_ = lean_array_push(v_sa_4934_, v___x_4939_);
v___x_4941_ = lean_array_push(v___x_4940_, v_e_4935_);
return v___x_4941_;
}
else
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
lean_dec_ref(v_sa_4934_);
lean_dec_ref(v_sep_4933_);
v___x_4942_ = lean_unsigned_to_nat(1u);
v___x_4943_ = lean_mk_empty_array_with_capacity(v___x_4942_);
v___x_4944_ = lean_array_push(v___x_4943_, v_e_4935_);
return v___x_4944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4945_, lean_object* v_sep_4946_, lean_object* v_sa_4947_, lean_object* v_e_4948_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4946_, v_sa_4947_, v_e_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4950_, lean_object* v_sep_4951_, lean_object* v_sa_4952_, lean_object* v_e_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Lean_Syntax_TSepArray_push(v_k_4950_, v_sep_4951_, v_sa_4952_, v_e_4953_);
lean_dec(v_k_4950_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4958_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4960_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4962_);
lean_dec_ref(v_sep_4962_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4967_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4969_, lean_object* v_k_4970_){
_start:
{
lean_object* v___x_4971_; 
v___x_4971_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4972_, lean_object* v_k_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4972_, v_k_4973_);
lean_dec_ref(v_k_4973_);
lean_dec(v_sep_4972_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4975_){
_start:
{
lean_inc_ref(v_v_4975_);
return v_v_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4976_);
lean_dec_ref(v_v_4976_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4980_; 
v___f_4980_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4983_, lean_object* v_sep_4984_){
_start:
{
lean_object* v___f_4985_; 
v___f_4985_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4986_, lean_object* v_sep_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4986_, v_sep_4987_);
lean_dec_ref(v_sep_4987_);
lean_dec(v_k_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4989_, lean_object* v_sep_4990_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4991_, 0, v_k_4989_);
lean_closure_set(v___x_4991_, 1, v_sep_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4992_, lean_object* v_x_4993_){
_start:
{
lean_object* v___x_4994_; 
v___x_4994_ = lean_apply_1(v_inst_4992_, v_x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v___x_4997_; size_t v_sz_4998_; size_t v___x_4999_; lean_object* v___x_5000_; 
v___x_4997_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4998_ = lean_array_size(v_a_4996_);
v___x_4999_ = ((size_t)0ULL);
v___x_5000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4997_, v___f_4995_, v_sz_4998_, v___x_4999_, v_a_4996_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5001_){
_start:
{
lean_object* v___f_5002_; lean_object* v___f_5003_; 
v___f_5002_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5002_, 0, v_inst_5001_);
v___f_5003_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5003_, 0, v___f_5002_);
return v___f_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5004_, lean_object* v_k_x27_5005_, lean_object* v_inst_5006_){
_start:
{
lean_object* v___x_5007_; 
v___x_5007_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5008_, lean_object* v_k_x27_5009_, lean_object* v_inst_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5008_, v_k_x27_5009_, v_inst_5010_);
lean_dec(v_k_x27_5009_);
lean_dec(v_k_5008_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_5012_){
_start:
{
lean_inc_ref(v_a_5012_);
return v_a_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_5013_);
lean_dec_ref(v_a_5013_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_5017_; 
v___f_5017_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5020_){
_start:
{
lean_object* v___f_5021_; 
v___f_5021_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5022_);
lean_dec(v_k_5022_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5030_){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5031_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5032_ = lean_box(2);
v___x_5033_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5034_ = lean_unsigned_to_nat(2u);
v___x_5035_ = lean_mk_empty_array_with_capacity(v___x_5034_);
v___x_5036_ = lean_array_push(v___x_5035_, v_id_5030_);
v___x_5037_ = lean_array_push(v___x_5036_, v___x_5033_);
v___x_5038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5032_);
lean_ctor_set(v___x_5038_, 1, v___x_5031_);
lean_ctor_set(v___x_5038_, 2, v___x_5037_);
return v___x_5038_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5042_; lean_object* v___x_5043_; 
v___x_5042_ = 123;
v___x_5043_ = lean_box_uint32(v___x_5042_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5044_, lean_object* v_i_5045_){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l_Lean_Syntax_decodeQuotedChar(v_s_5044_, v_i_5045_);
if (lean_obj_tag(v___x_5046_) == 0)
{
uint32_t v_c_5047_; uint32_t v___x_5048_; uint8_t v___x_5049_; 
v_c_5047_ = lean_string_utf8_get(v_s_5044_, v_i_5045_);
v___x_5048_ = 123;
v___x_5049_ = lean_uint32_dec_eq(v_c_5047_, v___x_5048_);
if (v___x_5049_ == 0)
{
return v___x_5046_;
}
else
{
lean_object* v_i_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_i_5050_ = lean_string_utf8_next(v_s_5044_, v_i_5045_);
v___x_5051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
lean_ctor_set(v___x_5052_, 1, v_i_5050_);
v___x_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
return v___x_5053_;
}
}
else
{
return v___x_5046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5054_, lean_object* v_i_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5054_, v_i_5055_);
lean_dec(v_i_5055_);
lean_dec_ref(v_s_5054_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5057_, lean_object* v_i_5058_, lean_object* v_acc_5059_){
_start:
{
uint32_t v_c_5060_; uint32_t v___x_5061_; uint8_t v___x_5062_; 
v_c_5060_ = lean_string_utf8_get(v_s_5057_, v_i_5058_);
v___x_5061_ = 34;
v___x_5062_ = lean_uint32_dec_eq(v_c_5060_, v___x_5061_);
if (v___x_5062_ == 0)
{
uint32_t v___x_5063_; uint8_t v___x_5064_; 
v___x_5063_ = 123;
v___x_5064_ = lean_uint32_dec_eq(v_c_5060_, v___x_5063_);
if (v___x_5064_ == 0)
{
lean_object* v_i_5065_; uint8_t v___x_5066_; 
v_i_5065_ = lean_string_utf8_next(v_s_5057_, v_i_5058_);
lean_dec(v_i_5058_);
v___x_5066_ = lean_string_utf8_at_end(v_s_5057_, v_i_5065_);
if (v___x_5066_ == 0)
{
uint32_t v___x_5067_; uint8_t v___x_5068_; 
v___x_5067_ = 92;
v___x_5068_ = lean_uint32_dec_eq(v_c_5060_, v___x_5067_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; 
v___x_5069_ = lean_string_push(v_acc_5059_, v_c_5060_);
v_i_5058_ = v_i_5065_;
v_acc_5059_ = v___x_5069_;
goto _start;
}
else
{
lean_object* v___x_5071_; 
v___x_5071_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5057_, v_i_5065_);
if (lean_obj_tag(v___x_5071_) == 1)
{
lean_object* v_val_5072_; lean_object* v_fst_5073_; lean_object* v_snd_5074_; uint32_t v___x_5075_; lean_object* v___x_5076_; 
lean_dec(v_i_5065_);
v_val_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc(v_val_5072_);
lean_dec_ref_known(v___x_5071_, 1);
v_fst_5073_ = lean_ctor_get(v_val_5072_, 0);
lean_inc(v_fst_5073_);
v_snd_5074_ = lean_ctor_get(v_val_5072_, 1);
lean_inc(v_snd_5074_);
lean_dec(v_val_5072_);
v___x_5075_ = lean_unbox_uint32(v_fst_5073_);
lean_dec(v_fst_5073_);
v___x_5076_ = lean_string_push(v_acc_5059_, v___x_5075_);
v_i_5058_ = v_snd_5074_;
v_acc_5059_ = v___x_5076_;
goto _start;
}
else
{
lean_object* v___x_5078_; 
lean_dec(v___x_5071_);
lean_inc_ref(v_s_5057_);
v___x_5078_ = l_Lean_Syntax_decodeStringGap(v_s_5057_, v_i_5065_);
lean_dec(v_i_5065_);
if (lean_obj_tag(v___x_5078_) == 1)
{
lean_object* v_val_5079_; 
v_val_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_val_5079_);
lean_dec_ref_known(v___x_5078_, 1);
v_i_5058_ = v_val_5079_;
goto _start;
}
else
{
lean_object* v___x_5081_; 
lean_dec(v___x_5078_);
lean_dec_ref(v_acc_5059_);
lean_dec_ref(v_s_5057_);
v___x_5081_ = lean_box(0);
return v___x_5081_;
}
}
}
}
else
{
lean_object* v___x_5082_; 
lean_dec(v_i_5065_);
lean_dec_ref(v_acc_5059_);
lean_dec_ref(v_s_5057_);
v___x_5082_ = lean_box(0);
return v___x_5082_;
}
}
else
{
lean_object* v___x_5083_; 
lean_dec(v_i_5058_);
lean_dec_ref(v_s_5057_);
v___x_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5083_, 0, v_acc_5059_);
return v___x_5083_;
}
}
else
{
lean_object* v___x_5084_; 
lean_dec(v_i_5058_);
lean_dec_ref(v_s_5057_);
v___x_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5084_, 0, v_acc_5059_);
return v___x_5084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5085_){
_start:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5086_ = lean_unsigned_to_nat(1u);
v___x_5087_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5088_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5085_, v___x_5086_, v___x_5087_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5092_){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5094_ = l_Lean_Syntax_isLit_x3f(v___x_5093_, v_stx_5092_);
if (lean_obj_tag(v___x_5094_) == 0)
{
return v___x_5094_;
}
else
{
lean_object* v_val_5095_; lean_object* v___x_5096_; 
v_val_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_val_5095_);
lean_dec_ref_known(v___x_5094_, 1);
v___x_5096_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5095_);
return v___x_5096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5097_);
lean_dec(v_stx_5097_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5099_){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5100_ = l_Lean_Syntax_getArgs(v_stx_5099_);
v___x_5101_ = lean_unsigned_to_nat(0u);
v___x_5102_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5103_ = lean_array_get_size(v___x_5100_);
v___x_5104_ = lean_nat_dec_lt(v___x_5101_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_dec_ref(v___x_5100_);
return v___x_5102_;
}
else
{
lean_object* v___x_5105_; lean_object* v___x_5106_; size_t v___x_5107_; size_t v___x_5108_; lean_object* v___x_5109_; lean_object* v_snd_5110_; 
v___x_5105_ = lean_box(v___x_5104_);
v___x_5106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
lean_ctor_set(v___x_5106_, 1, v___x_5102_);
v___x_5107_ = ((size_t)0ULL);
v___x_5108_ = lean_usize_of_nat(v___x_5103_);
v___x_5109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5100_, v___x_5107_, v___x_5108_, v___x_5106_);
lean_dec_ref(v___x_5100_);
v_snd_5110_ = lean_ctor_get(v___x_5109_, 1);
lean_inc(v_snd_5110_);
lean_dec_ref(v___x_5109_);
return v_snd_5110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Syntax_getSepArgs(v_stx_5111_);
lean_dec(v_stx_5111_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5113_, lean_object* v_mkElem_5114_, lean_object* v_mkLit_5115_, lean_object* v_as_5116_, size_t v_sz_5117_, size_t v_i_5118_, lean_object* v_b_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_a_5123_; lean_object* v_a_5124_; lean_object* v_elem_5129_; lean_object* v___y_5130_; lean_object* v___y_5131_; uint8_t v___x_5136_; 
v___x_5136_ = lean_usize_dec_lt(v_i_5118_, v_sz_5117_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5137_; 
lean_dec_ref(v_mkLit_5115_);
lean_dec_ref(v_mkElem_5114_);
lean_dec_ref(v_mkAppend_5113_);
v___x_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5137_, 0, v_b_5119_);
lean_ctor_set(v___x_5137_, 1, v___y_5121_);
return v___x_5137_;
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5139_; 
v_a_5138_ = lean_array_uget_borrowed(v_as_5116_, v_i_5118_);
v___x_5139_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5138_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_methods_5140_; lean_object* v_quotContext_5141_; lean_object* v_currMacroScope_5142_; lean_object* v_currRecDepth_5143_; lean_object* v_maxRecDepth_5144_; lean_object* v_ref_5145_; lean_object* v_ref_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v_methods_5140_ = lean_ctor_get(v___y_5120_, 0);
v_quotContext_5141_ = lean_ctor_get(v___y_5120_, 1);
v_currMacroScope_5142_ = lean_ctor_get(v___y_5120_, 2);
v_currRecDepth_5143_ = lean_ctor_get(v___y_5120_, 3);
v_maxRecDepth_5144_ = lean_ctor_get(v___y_5120_, 4);
v_ref_5145_ = lean_ctor_get(v___y_5120_, 5);
v_ref_5146_ = l_Lean_replaceRef(v_a_5138_, v_ref_5145_);
lean_inc(v_maxRecDepth_5144_);
lean_inc(v_currRecDepth_5143_);
lean_inc(v_currMacroScope_5142_);
lean_inc(v_quotContext_5141_);
lean_inc(v_methods_5140_);
v___x_5147_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5147_, 0, v_methods_5140_);
lean_ctor_set(v___x_5147_, 1, v_quotContext_5141_);
lean_ctor_set(v___x_5147_, 2, v_currMacroScope_5142_);
lean_ctor_set(v___x_5147_, 3, v_currRecDepth_5143_);
lean_ctor_set(v___x_5147_, 4, v_maxRecDepth_5144_);
lean_ctor_set(v___x_5147_, 5, v_ref_5146_);
lean_inc_ref(v_mkElem_5114_);
lean_inc(v_a_5138_);
v___x_5148_ = lean_apply_3(v_mkElem_5114_, v_a_5138_, v___x_5147_, v___y_5121_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v_a_5150_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_a_5149_);
v_a_5150_ = lean_ctor_get(v___x_5148_, 1);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5148_, 2);
v_elem_5129_ = v_a_5149_;
v___y_5130_ = v___y_5120_;
v___y_5131_ = v_a_5150_;
goto v___jp_5128_;
}
else
{
lean_dec(v_b_5119_);
lean_dec_ref(v_mkLit_5115_);
lean_dec_ref(v_mkElem_5114_);
lean_dec_ref(v_mkAppend_5113_);
return v___x_5148_;
}
}
else
{
lean_object* v_val_5151_; uint8_t v___x_5152_; 
v_val_5151_ = lean_ctor_get(v___x_5139_, 0);
lean_inc_n(v_val_5151_, 2);
lean_dec_ref_known(v___x_5139_, 1);
v___x_5152_ = lean_string_isempty(v_val_5151_);
if (v___x_5152_ == 0)
{
lean_object* v_methods_5153_; lean_object* v_quotContext_5154_; lean_object* v_currMacroScope_5155_; lean_object* v_currRecDepth_5156_; lean_object* v_maxRecDepth_5157_; lean_object* v_ref_5158_; lean_object* v_ref_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
v_methods_5153_ = lean_ctor_get(v___y_5120_, 0);
v_quotContext_5154_ = lean_ctor_get(v___y_5120_, 1);
v_currMacroScope_5155_ = lean_ctor_get(v___y_5120_, 2);
v_currRecDepth_5156_ = lean_ctor_get(v___y_5120_, 3);
v_maxRecDepth_5157_ = lean_ctor_get(v___y_5120_, 4);
v_ref_5158_ = lean_ctor_get(v___y_5120_, 5);
v_ref_5159_ = l_Lean_replaceRef(v_a_5138_, v_ref_5158_);
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
lean_inc_ref(v_mkLit_5115_);
v___x_5161_ = lean_apply_3(v_mkLit_5115_, v_val_5151_, v___x_5160_, v___y_5121_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v_a_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
v_a_5163_ = lean_ctor_get(v___x_5161_, 1);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5161_, 2);
v_elem_5129_ = v_a_5162_;
v___y_5130_ = v___y_5120_;
v___y_5131_ = v_a_5163_;
goto v___jp_5128_;
}
else
{
lean_dec(v_b_5119_);
lean_dec_ref(v_mkLit_5115_);
lean_dec_ref(v_mkElem_5114_);
lean_dec_ref(v_mkAppend_5113_);
return v___x_5161_;
}
}
else
{
lean_dec(v_val_5151_);
v_a_5123_ = v_b_5119_;
v_a_5124_ = v___y_5121_;
goto v___jp_5122_;
}
}
}
v___jp_5122_:
{
size_t v___x_5125_; size_t v___x_5126_; 
v___x_5125_ = ((size_t)1ULL);
v___x_5126_ = lean_usize_add(v_i_5118_, v___x_5125_);
v_i_5118_ = v___x_5126_;
v_b_5119_ = v_a_5123_;
v___y_5121_ = v_a_5124_;
goto _start;
}
v___jp_5128_:
{
uint8_t v___x_5132_; 
v___x_5132_ = l_Lean_Syntax_isMissing(v_b_5119_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; 
lean_inc_ref(v_mkAppend_5113_);
lean_inc_ref(v___y_5130_);
v___x_5133_ = lean_apply_4(v_mkAppend_5113_, v_b_5119_, v_elem_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; lean_object* v_a_5135_; 
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
lean_inc(v_a_5134_);
v_a_5135_ = lean_ctor_get(v___x_5133_, 1);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5133_, 2);
v_a_5123_ = v_a_5134_;
v_a_5124_ = v_a_5135_;
goto v___jp_5122_;
}
else
{
lean_dec_ref(v_mkLit_5115_);
lean_dec_ref(v_mkElem_5114_);
lean_dec_ref(v_mkAppend_5113_);
return v___x_5133_;
}
}
else
{
lean_dec(v_b_5119_);
v_a_5123_ = v_elem_5129_;
v_a_5124_ = v___y_5131_;
goto v___jp_5122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5164_, lean_object* v_mkElem_5165_, lean_object* v_mkLit_5166_, lean_object* v_as_5167_, lean_object* v_sz_5168_, lean_object* v_i_5169_, lean_object* v_b_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
size_t v_sz_boxed_5173_; size_t v_i_boxed_5174_; lean_object* v_res_5175_; 
v_sz_boxed_5173_ = lean_unbox_usize(v_sz_5168_);
lean_dec(v_sz_5168_);
v_i_boxed_5174_ = lean_unbox_usize(v_i_5169_);
lean_dec(v_i_5169_);
v_res_5175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5164_, v_mkElem_5165_, v_mkLit_5166_, v_as_5167_, v_sz_boxed_5173_, v_i_boxed_5174_, v_b_5170_, v___y_5171_, v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec_ref(v_as_5167_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5176_, lean_object* v_mkAppend_5177_, lean_object* v_mkElem_5178_, lean_object* v_mkLit_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_){
_start:
{
lean_object* v_result_5182_; size_t v_sz_5183_; size_t v___x_5184_; lean_object* v___x_5185_; 
v_result_5182_ = lean_box(0);
v_sz_5183_ = lean_array_size(v_chunks_5176_);
v___x_5184_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5179_);
v___x_5185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5177_, v_mkElem_5178_, v_mkLit_5179_, v_chunks_5176_, v_sz_5183_, v___x_5184_, v_result_5182_, v_a_5180_, v_a_5181_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; lean_object* v_a_5187_; uint8_t v___x_5188_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
v_a_5187_ = lean_ctor_get(v___x_5185_, 1);
v___x_5188_ = l_Lean_Syntax_isMissing(v_a_5186_);
if (v___x_5188_ == 0)
{
lean_dec_ref(v_mkLit_5179_);
return v___x_5185_;
}
else
{
lean_object* v___x_5189_; lean_object* v___x_5190_; 
lean_inc(v_a_5187_);
lean_dec_ref_known(v___x_5185_, 2);
v___x_5189_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5180_);
v___x_5190_ = lean_apply_3(v_mkLit_5179_, v___x_5189_, v_a_5180_, v_a_5187_);
return v___x_5190_;
}
}
else
{
lean_dec_ref(v_mkLit_5179_);
return v___x_5185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5191_, lean_object* v_mkAppend_5192_, lean_object* v_mkElem_5193_, lean_object* v_mkLit_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5191_, v_mkAppend_5192_, v_mkElem_5193_, v_mkLit_5194_, v_a_5195_, v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec_ref(v_chunks_5191_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5202_, lean_object* v_b_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v_ref_5206_; uint8_t v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v_ref_5206_ = lean_ctor_get(v___y_5204_, 5);
v___x_5207_ = 0;
v___x_5208_ = l_Lean_SourceInfo_fromRef(v_ref_5206_, v___x_5207_);
v___x_5209_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5210_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5208_);
v___x_5211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5208_);
lean_ctor_set(v___x_5211_, 1, v___x_5210_);
v___x_5212_ = l_Lean_Syntax_node3(v___x_5208_, v___x_5209_, v_a_5202_, v___x_5211_, v_b_5203_);
v___x_5213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5212_);
lean_ctor_set(v___x_5213_, 1, v___y_5205_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5214_, lean_object* v_b_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5214_, v_b_5215_, v___y_5216_, v___y_5217_);
lean_dec_ref(v___y_5216_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5219_, lean_object* v_a_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_ref_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v_ref_5223_ = lean_ctor_get(v___y_5221_, 5);
v___x_5224_ = 0;
v___x_5225_ = l_Lean_SourceInfo_fromRef(v_ref_5223_, v___x_5224_);
v___x_5226_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5227_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5225_);
v___x_5228_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5227_, v_a_5220_);
v___x_5229_ = l_Lean_Syntax_node2(v___x_5225_, v___x_5226_, v_ofInterpFn_5219_, v___x_5228_);
v___x_5230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5229_);
lean_ctor_set(v___x_5230_, 1, v___y_5222_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5231_, lean_object* v_a_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5231_, v_a_5232_, v___y_5233_, v___y_5234_);
lean_dec_ref(v___y_5233_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5236_, lean_object* v_s_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
lean_object* v_ref_5240_; uint8_t v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v_ref_5240_ = lean_ctor_get(v___y_5238_, 5);
v___x_5241_ = 0;
v___x_5242_ = l_Lean_SourceInfo_fromRef(v_ref_5240_, v___x_5241_);
v___x_5243_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5244_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5245_ = lean_box(2);
v___x_5246_ = l_Lean_Syntax_mkStrLit(v_s_5237_, v___x_5245_);
lean_inc(v___x_5242_);
v___x_5247_ = l_Lean_Syntax_node1(v___x_5242_, v___x_5244_, v___x_5246_);
v___x_5248_ = l_Lean_Syntax_node2(v___x_5242_, v___x_5243_, v_ofLitFn_5236_, v___x_5247_);
v___x_5249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5248_);
lean_ctor_set(v___x_5249_, 1, v___y_5239_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5250_, lean_object* v_s_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5250_, v_s_5251_, v___y_5252_, v___y_5253_);
lean_dec_ref(v___y_5252_);
return v_res_5254_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5273_ = l_String_toRawSubstring_x27(v___x_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5294_, lean_object* v_type_5295_, lean_object* v_ofInterpFn_5296_, lean_object* v_ofLitFn_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_){
_start:
{
lean_object* v___f_5300_; lean_object* v___f_5301_; lean_object* v___f_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___f_5300_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5301_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5301_, 0, v_ofInterpFn_5296_);
v___f_5302_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5302_, 0, v_ofLitFn_5297_);
v___x_5303_ = l_Lean_Syntax_getArgs(v_interpStr_5294_);
v___x_5304_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5303_, v___f_5300_, v___f_5301_, v___f_5302_, v_a_5298_, v_a_5299_);
lean_dec_ref(v___x_5303_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5337_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
v_a_5306_ = lean_ctor_get(v___x_5304_, 1);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5308_ = v___x_5304_;
v_isShared_5309_ = v_isSharedCheck_5337_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_inc(v_a_5305_);
lean_dec(v___x_5304_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5337_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v_quotContext_5310_; lean_object* v_currMacroScope_5311_; lean_object* v_ref_5312_; uint8_t v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5335_; 
v_quotContext_5310_ = lean_ctor_get(v_a_5298_, 1);
v_currMacroScope_5311_ = lean_ctor_get(v_a_5298_, 2);
v_ref_5312_ = lean_ctor_get(v_a_5298_, 5);
v___x_5313_ = 0;
v___x_5314_ = l_Lean_SourceInfo_fromRef(v_ref_5312_, v___x_5313_);
v___x_5315_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5316_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5317_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5314_, 7);
v___x_5318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5314_);
lean_ctor_set(v___x_5318_, 1, v___x_5317_);
v___x_5319_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5320_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5321_ = lean_box(0);
lean_inc(v_currMacroScope_5311_);
lean_inc(v_quotContext_5310_);
v___x_5322_ = l_Lean_addMacroScope(v_quotContext_5310_, v___x_5321_, v_currMacroScope_5311_);
v___x_5323_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5324_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5314_);
lean_ctor_set(v___x_5324_, 1, v___x_5320_);
lean_ctor_set(v___x_5324_, 2, v___x_5322_);
lean_ctor_set(v___x_5324_, 3, v___x_5323_);
v___x_5325_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5319_, v___x_5324_);
v___x_5326_ = l_Lean_Syntax_node2(v___x_5314_, v___x_5316_, v___x_5318_, v___x_5325_);
v___x_5327_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5314_);
lean_ctor_set(v___x_5328_, 1, v___x_5327_);
v___x_5329_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5330_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5329_, v_type_5295_);
v___x_5331_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5314_);
lean_ctor_set(v___x_5332_, 1, v___x_5331_);
v___x_5333_ = l_Lean_Syntax_node5(v___x_5314_, v___x_5315_, v___x_5326_, v_a_5305_, v___x_5328_, v___x_5330_, v___x_5332_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5333_);
v___x_5335_ = v___x_5308_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5333_);
lean_ctor_set(v_reuseFailAlloc_5336_, 1, v_a_5306_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
else
{
lean_object* v_a_5338_; lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_dec(v_type_5295_);
v_a_5338_ = lean_ctor_get(v___x_5304_, 0);
v_a_5339_ = lean_ctor_get(v___x_5304_, 1);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5304_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_inc(v_a_5338_);
lean_dec(v___x_5304_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5338_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5347_, lean_object* v_type_5348_, lean_object* v_ofInterpFn_5349_, lean_object* v_ofLitFn_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5347_, v_type_5348_, v_ofInterpFn_5349_, v_ofLitFn_5350_, v_a_5351_, v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_interpStr_5347_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5354_){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = lean_unsigned_to_nat(1u);
v___x_5356_ = l_Lean_Syntax_getArg(v_stx_5354_, v___x_5355_);
if (lean_obj_tag(v___x_5356_) == 1)
{
lean_object* v_kind_5357_; 
v_kind_5357_ = lean_ctor_get(v___x_5356_, 1);
lean_inc(v_kind_5357_);
if (lean_obj_tag(v_kind_5357_) == 1)
{
lean_object* v_pre_5358_; 
v_pre_5358_ = lean_ctor_get(v_kind_5357_, 0);
lean_inc(v_pre_5358_);
if (lean_obj_tag(v_pre_5358_) == 1)
{
lean_object* v_pre_5359_; 
v_pre_5359_ = lean_ctor_get(v_pre_5358_, 0);
lean_inc(v_pre_5359_);
if (lean_obj_tag(v_pre_5359_) == 1)
{
lean_object* v_pre_5360_; 
v_pre_5360_ = lean_ctor_get(v_pre_5359_, 0);
lean_inc(v_pre_5360_);
if (lean_obj_tag(v_pre_5360_) == 1)
{
lean_object* v_pre_5361_; 
v_pre_5361_ = lean_ctor_get(v_pre_5360_, 0);
if (lean_obj_tag(v_pre_5361_) == 0)
{
lean_object* v_args_5362_; lean_object* v_str_5363_; lean_object* v_str_5364_; lean_object* v_str_5365_; lean_object* v_str_5366_; lean_object* v___x_5367_; uint8_t v___x_5368_; 
v_args_5362_ = lean_ctor_get(v___x_5356_, 2);
lean_inc_ref(v_args_5362_);
lean_dec_ref_known(v___x_5356_, 3);
v_str_5363_ = lean_ctor_get(v_kind_5357_, 1);
lean_inc_ref(v_str_5363_);
lean_dec_ref_known(v_kind_5357_, 2);
v_str_5364_ = lean_ctor_get(v_pre_5358_, 1);
lean_inc_ref(v_str_5364_);
lean_dec_ref_known(v_pre_5358_, 2);
v_str_5365_ = lean_ctor_get(v_pre_5359_, 1);
lean_inc_ref(v_str_5365_);
lean_dec_ref_known(v_pre_5359_, 2);
v_str_5366_ = lean_ctor_get(v_pre_5360_, 1);
lean_inc_ref(v_str_5366_);
lean_dec_ref_known(v_pre_5360_, 2);
v___x_5367_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5368_ = lean_string_dec_eq(v_str_5366_, v___x_5367_);
lean_dec_ref(v_str_5366_);
if (v___x_5368_ == 0)
{
lean_object* v___x_5369_; 
lean_dec_ref(v_str_5365_);
lean_dec_ref(v_str_5364_);
lean_dec_ref(v_str_5363_);
lean_dec_ref(v_args_5362_);
v___x_5369_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5369_;
}
else
{
lean_object* v___x_5370_; uint8_t v___x_5371_; 
v___x_5370_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5371_ = lean_string_dec_eq(v_str_5365_, v___x_5370_);
lean_dec_ref(v_str_5365_);
if (v___x_5371_ == 0)
{
lean_object* v___x_5372_; 
lean_dec_ref(v_str_5364_);
lean_dec_ref(v_str_5363_);
lean_dec_ref(v_args_5362_);
v___x_5372_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5372_;
}
else
{
lean_object* v___x_5373_; uint8_t v___x_5374_; 
v___x_5373_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5374_ = lean_string_dec_eq(v_str_5364_, v___x_5373_);
lean_dec_ref(v_str_5364_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; 
lean_dec_ref(v_str_5363_);
lean_dec_ref(v_args_5362_);
v___x_5375_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5375_;
}
else
{
lean_object* v___x_5376_; uint8_t v___x_5377_; 
v___x_5376_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5377_ = lean_string_dec_eq(v_str_5363_, v___x_5376_);
lean_dec_ref(v_str_5363_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; 
lean_dec_ref(v_args_5362_);
v___x_5378_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5378_;
}
else
{
lean_object* v___x_5379_; lean_object* v___x_5380_; uint8_t v___x_5381_; 
v___x_5379_ = lean_array_get_size(v_args_5362_);
v___x_5380_ = lean_unsigned_to_nat(2u);
v___x_5381_ = lean_nat_dec_eq(v___x_5379_, v___x_5380_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
lean_dec_ref(v_args_5362_);
v___x_5382_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5382_;
}
else
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = lean_unsigned_to_nat(0u);
v___x_5384_ = lean_array_fget(v_args_5362_, v___x_5383_);
lean_dec_ref(v_args_5362_);
if (lean_obj_tag(v___x_5384_) == 2)
{
lean_object* v_val_5385_; 
v_val_5385_ = lean_ctor_get(v___x_5384_, 1);
lean_inc_ref(v_val_5385_);
lean_dec_ref_known(v___x_5384_, 2);
return v_val_5385_;
}
else
{
lean_object* v___x_5386_; 
lean_dec(v___x_5384_);
v___x_5386_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5386_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5387_; 
lean_dec_ref_known(v_pre_5360_, 2);
lean_dec_ref_known(v_pre_5359_, 2);
lean_dec_ref_known(v_pre_5358_, 2);
lean_dec_ref_known(v_kind_5357_, 2);
lean_dec_ref_known(v___x_5356_, 3);
v___x_5387_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5387_;
}
}
else
{
lean_object* v___x_5388_; 
lean_dec(v_pre_5360_);
lean_dec_ref_known(v_pre_5359_, 2);
lean_dec_ref_known(v_pre_5358_, 2);
lean_dec_ref_known(v_kind_5357_, 2);
lean_dec_ref_known(v___x_5356_, 3);
v___x_5388_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5388_;
}
}
else
{
lean_object* v___x_5389_; 
lean_dec(v_pre_5359_);
lean_dec_ref_known(v_pre_5358_, 2);
lean_dec_ref_known(v_kind_5357_, 2);
lean_dec_ref_known(v___x_5356_, 3);
v___x_5389_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5389_;
}
}
else
{
lean_object* v___x_5390_; 
lean_dec_ref_known(v_kind_5357_, 2);
lean_dec(v_pre_5358_);
lean_dec_ref_known(v___x_5356_, 3);
v___x_5390_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5390_;
}
}
else
{
lean_object* v___x_5391_; 
lean_dec(v_kind_5357_);
lean_dec_ref_known(v___x_5356_, 3);
v___x_5391_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5391_;
}
}
else
{
lean_object* v___x_5392_; 
lean_dec(v___x_5356_);
v___x_5392_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_TSyntax_getDocString(v_stx_5393_);
lean_dec(v_stx_5393_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5413_, lean_object* v_prec_5414_){
_start:
{
lean_object* v___y_5416_; lean_object* v___y_5423_; lean_object* v___y_5430_; lean_object* v___y_5437_; lean_object* v___y_5444_; lean_object* v___y_5451_; 
switch(v_x_5413_)
{
case 0:
{
lean_object* v___x_5457_; uint8_t v___x_5458_; 
v___x_5457_ = lean_unsigned_to_nat(1024u);
v___x_5458_ = lean_nat_dec_le(v___x_5457_, v_prec_5414_);
if (v___x_5458_ == 0)
{
lean_object* v___x_5459_; 
v___x_5459_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5416_ = v___x_5459_;
goto v___jp_5415_;
}
else
{
lean_object* v___x_5460_; 
v___x_5460_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5416_ = v___x_5460_;
goto v___jp_5415_;
}
}
case 1:
{
lean_object* v___x_5461_; uint8_t v___x_5462_; 
v___x_5461_ = lean_unsigned_to_nat(1024u);
v___x_5462_ = lean_nat_dec_le(v___x_5461_, v_prec_5414_);
if (v___x_5462_ == 0)
{
lean_object* v___x_5463_; 
v___x_5463_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5423_ = v___x_5463_;
goto v___jp_5422_;
}
else
{
lean_object* v___x_5464_; 
v___x_5464_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5423_ = v___x_5464_;
goto v___jp_5422_;
}
}
case 2:
{
lean_object* v___x_5465_; uint8_t v___x_5466_; 
v___x_5465_ = lean_unsigned_to_nat(1024u);
v___x_5466_ = lean_nat_dec_le(v___x_5465_, v_prec_5414_);
if (v___x_5466_ == 0)
{
lean_object* v___x_5467_; 
v___x_5467_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5430_ = v___x_5467_;
goto v___jp_5429_;
}
else
{
lean_object* v___x_5468_; 
v___x_5468_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5430_ = v___x_5468_;
goto v___jp_5429_;
}
}
case 3:
{
lean_object* v___x_5469_; uint8_t v___x_5470_; 
v___x_5469_ = lean_unsigned_to_nat(1024u);
v___x_5470_ = lean_nat_dec_le(v___x_5469_, v_prec_5414_);
if (v___x_5470_ == 0)
{
lean_object* v___x_5471_; 
v___x_5471_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5437_ = v___x_5471_;
goto v___jp_5436_;
}
else
{
lean_object* v___x_5472_; 
v___x_5472_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5437_ = v___x_5472_;
goto v___jp_5436_;
}
}
case 4:
{
lean_object* v___x_5473_; uint8_t v___x_5474_; 
v___x_5473_ = lean_unsigned_to_nat(1024u);
v___x_5474_ = lean_nat_dec_le(v___x_5473_, v_prec_5414_);
if (v___x_5474_ == 0)
{
lean_object* v___x_5475_; 
v___x_5475_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5444_ = v___x_5475_;
goto v___jp_5443_;
}
else
{
lean_object* v___x_5476_; 
v___x_5476_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5444_ = v___x_5476_;
goto v___jp_5443_;
}
}
default: 
{
lean_object* v___x_5477_; uint8_t v___x_5478_; 
v___x_5477_ = lean_unsigned_to_nat(1024u);
v___x_5478_ = lean_nat_dec_le(v___x_5477_, v_prec_5414_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; 
v___x_5479_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5451_ = v___x_5479_;
goto v___jp_5450_;
}
else
{
lean_object* v___x_5480_; 
v___x_5480_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5451_ = v___x_5480_;
goto v___jp_5450_;
}
}
}
v___jp_5415_:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5417_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5416_);
v___x_5418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___y_5416_);
lean_ctor_set(v___x_5418_, 1, v___x_5417_);
v___x_5419_ = 0;
v___x_5420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5420_, 0, v___x_5418_);
lean_ctor_set_uint8(v___x_5420_, sizeof(void*)*1, v___x_5419_);
v___x_5421_ = l_Repr_addAppParen(v___x_5420_, v_prec_5414_);
return v___x_5421_;
}
v___jp_5422_:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; uint8_t v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5424_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5423_);
v___x_5425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5425_, 0, v___y_5423_);
lean_ctor_set(v___x_5425_, 1, v___x_5424_);
v___x_5426_ = 0;
v___x_5427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5427_, 0, v___x_5425_);
lean_ctor_set_uint8(v___x_5427_, sizeof(void*)*1, v___x_5426_);
v___x_5428_ = l_Repr_addAppParen(v___x_5427_, v_prec_5414_);
return v___x_5428_;
}
v___jp_5429_:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5431_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5430_);
v___x_5432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___y_5430_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = 0;
v___x_5434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5434_, 0, v___x_5432_);
lean_ctor_set_uint8(v___x_5434_, sizeof(void*)*1, v___x_5433_);
v___x_5435_ = l_Repr_addAppParen(v___x_5434_, v_prec_5414_);
return v___x_5435_;
}
v___jp_5436_:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; uint8_t v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5438_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5437_);
v___x_5439_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5439_, 0, v___y_5437_);
lean_ctor_set(v___x_5439_, 1, v___x_5438_);
v___x_5440_ = 0;
v___x_5441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5441_, 0, v___x_5439_);
lean_ctor_set_uint8(v___x_5441_, sizeof(void*)*1, v___x_5440_);
v___x_5442_ = l_Repr_addAppParen(v___x_5441_, v_prec_5414_);
return v___x_5442_;
}
v___jp_5443_:
{
lean_object* v___x_5445_; lean_object* v___x_5446_; uint8_t v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; 
v___x_5445_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5444_);
v___x_5446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5446_, 0, v___y_5444_);
lean_ctor_set(v___x_5446_, 1, v___x_5445_);
v___x_5447_ = 0;
v___x_5448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5448_, 0, v___x_5446_);
lean_ctor_set_uint8(v___x_5448_, sizeof(void*)*1, v___x_5447_);
v___x_5449_ = l_Repr_addAppParen(v___x_5448_, v_prec_5414_);
return v___x_5449_;
}
v___jp_5450_:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; uint8_t v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5452_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5451_);
v___x_5453_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5453_, 0, v___y_5451_);
lean_ctor_set(v___x_5453_, 1, v___x_5452_);
v___x_5454_ = 0;
v___x_5455_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5455_, 0, v___x_5453_);
lean_ctor_set_uint8(v___x_5455_, sizeof(void*)*1, v___x_5454_);
v___x_5456_ = l_Repr_addAppParen(v___x_5455_, v_prec_5414_);
return v___x_5456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5481_, lean_object* v_prec_5482_){
_start:
{
uint8_t v_x_329__boxed_5483_; lean_object* v_res_5484_; 
v_x_329__boxed_5483_ = lean_unbox(v_x_5481_);
v_res_5484_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5483_, v_prec_5482_);
lean_dec(v_prec_5482_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5496_, lean_object* v_prec_5497_){
_start:
{
lean_object* v___y_5499_; lean_object* v___y_5506_; lean_object* v___y_5513_; 
switch(v_x_5496_)
{
case 0:
{
lean_object* v___x_5519_; uint8_t v___x_5520_; 
v___x_5519_ = lean_unsigned_to_nat(1024u);
v___x_5520_ = lean_nat_dec_le(v___x_5519_, v_prec_5497_);
if (v___x_5520_ == 0)
{
lean_object* v___x_5521_; 
v___x_5521_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5499_ = v___x_5521_;
goto v___jp_5498_;
}
else
{
lean_object* v___x_5522_; 
v___x_5522_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5499_ = v___x_5522_;
goto v___jp_5498_;
}
}
case 1:
{
lean_object* v___x_5523_; uint8_t v___x_5524_; 
v___x_5523_ = lean_unsigned_to_nat(1024u);
v___x_5524_ = lean_nat_dec_le(v___x_5523_, v_prec_5497_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5525_; 
v___x_5525_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5506_ = v___x_5525_;
goto v___jp_5505_;
}
else
{
lean_object* v___x_5526_; 
v___x_5526_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5506_ = v___x_5526_;
goto v___jp_5505_;
}
}
default: 
{
lean_object* v___x_5527_; uint8_t v___x_5528_; 
v___x_5527_ = lean_unsigned_to_nat(1024u);
v___x_5528_ = lean_nat_dec_le(v___x_5527_, v_prec_5497_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; 
v___x_5529_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5513_ = v___x_5529_;
goto v___jp_5512_;
}
else
{
lean_object* v___x_5530_; 
v___x_5530_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5513_ = v___x_5530_;
goto v___jp_5512_;
}
}
}
v___jp_5498_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; uint8_t v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; 
v___x_5500_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5499_);
v___x_5501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5501_, 0, v___y_5499_);
lean_ctor_set(v___x_5501_, 1, v___x_5500_);
v___x_5502_ = 0;
v___x_5503_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5503_, 0, v___x_5501_);
lean_ctor_set_uint8(v___x_5503_, sizeof(void*)*1, v___x_5502_);
v___x_5504_ = l_Repr_addAppParen(v___x_5503_, v_prec_5497_);
return v___x_5504_;
}
v___jp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; uint8_t v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5507_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5506_);
v___x_5508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5508_, 0, v___y_5506_);
lean_ctor_set(v___x_5508_, 1, v___x_5507_);
v___x_5509_ = 0;
v___x_5510_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5510_, 0, v___x_5508_);
lean_ctor_set_uint8(v___x_5510_, sizeof(void*)*1, v___x_5509_);
v___x_5511_ = l_Repr_addAppParen(v___x_5510_, v_prec_5497_);
return v___x_5511_;
}
v___jp_5512_:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; uint8_t v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; 
v___x_5514_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5513_);
v___x_5515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5515_, 0, v___y_5513_);
lean_ctor_set(v___x_5515_, 1, v___x_5514_);
v___x_5516_ = 0;
v___x_5517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5517_, 0, v___x_5515_);
lean_ctor_set_uint8(v___x_5517_, sizeof(void*)*1, v___x_5516_);
v___x_5518_ = l_Repr_addAppParen(v___x_5517_, v_prec_5497_);
return v___x_5518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5531_, lean_object* v_prec_5532_){
_start:
{
uint8_t v_x_167__boxed_5533_; lean_object* v_res_5534_; 
v_x_167__boxed_5533_ = lean_unbox(v_x_5531_);
v_res_5534_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5533_, v_prec_5532_);
lean_dec(v_prec_5532_);
return v_res_5534_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5546_ = lean_unsigned_to_nat(8u);
v___x_5547_ = lean_nat_to_int(v___x_5546_);
return v___x_5547_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5557_ = lean_unsigned_to_nat(13u);
v___x_5558_ = lean_nat_to_int(v___x_5557_);
return v___x_5558_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5568_ = lean_unsigned_to_nat(10u);
v___x_5569_ = lean_nat_to_int(v___x_5568_);
return v___x_5569_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5573_ = lean_unsigned_to_nat(14u);
v___x_5574_ = lean_nat_to_int(v___x_5573_);
return v___x_5574_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = lean_unsigned_to_nat(19u);
v___x_5579_ = lean_nat_to_int(v___x_5578_);
return v___x_5579_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; 
v___x_5583_ = lean_unsigned_to_nat(20u);
v___x_5584_ = lean_nat_to_int(v___x_5583_);
return v___x_5584_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5591_ = lean_unsigned_to_nat(9u);
v___x_5592_ = lean_nat_to_int(v___x_5591_);
return v___x_5592_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5599_ = lean_unsigned_to_nat(12u);
v___x_5600_ = lean_nat_to_int(v___x_5599_);
return v___x_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5607_){
_start:
{
uint8_t v_zeta_5608_; uint8_t v_beta_5609_; uint8_t v_eta_5610_; uint8_t v_etaStruct_5611_; uint8_t v_iota_5612_; uint8_t v_proj_5613_; uint8_t v_decide_5614_; uint8_t v_autoUnfold_5615_; uint8_t v_failIfUnchanged_5616_; uint8_t v_unfoldPartialApp_5617_; uint8_t v_zetaDelta_5618_; uint8_t v_index_5619_; uint8_t v_zetaUnused_5620_; uint8_t v_zetaHave_5621_; uint8_t v_locals_5622_; uint8_t v_instances_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; uint8_t v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
v_zeta_5608_ = lean_ctor_get_uint8(v_x_5607_, 0);
v_beta_5609_ = lean_ctor_get_uint8(v_x_5607_, 1);
v_eta_5610_ = lean_ctor_get_uint8(v_x_5607_, 2);
v_etaStruct_5611_ = lean_ctor_get_uint8(v_x_5607_, 3);
v_iota_5612_ = lean_ctor_get_uint8(v_x_5607_, 4);
v_proj_5613_ = lean_ctor_get_uint8(v_x_5607_, 5);
v_decide_5614_ = lean_ctor_get_uint8(v_x_5607_, 6);
v_autoUnfold_5615_ = lean_ctor_get_uint8(v_x_5607_, 7);
v_failIfUnchanged_5616_ = lean_ctor_get_uint8(v_x_5607_, 8);
v_unfoldPartialApp_5617_ = lean_ctor_get_uint8(v_x_5607_, 9);
v_zetaDelta_5618_ = lean_ctor_get_uint8(v_x_5607_, 10);
v_index_5619_ = lean_ctor_get_uint8(v_x_5607_, 11);
v_zetaUnused_5620_ = lean_ctor_get_uint8(v_x_5607_, 12);
v_zetaHave_5621_ = lean_ctor_get_uint8(v_x_5607_, 13);
v_locals_5622_ = lean_ctor_get_uint8(v_x_5607_, 14);
v_instances_5623_ = lean_ctor_get_uint8(v_x_5607_, 15);
v___x_5624_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5625_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5626_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5627_ = lean_unsigned_to_nat(0u);
v___x_5628_ = l_Bool_repr___redArg(v_zeta_5608_);
v___x_5629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5626_);
lean_ctor_set(v___x_5629_, 1, v___x_5628_);
v___x_5630_ = 0;
v___x_5631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5631_, 0, v___x_5629_);
lean_ctor_set_uint8(v___x_5631_, sizeof(void*)*1, v___x_5630_);
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5625_);
lean_ctor_set(v___x_5632_, 1, v___x_5631_);
v___x_5633_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5632_);
lean_ctor_set(v___x_5634_, 1, v___x_5633_);
v___x_5635_ = lean_box(1);
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5636_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
lean_ctor_set(v___x_5639_, 1, v___x_5624_);
v___x_5640_ = l_Bool_repr___redArg(v_beta_5609_);
v___x_5641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5626_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
lean_ctor_set_uint8(v___x_5642_, sizeof(void*)*1, v___x_5630_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5639_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5643_);
lean_ctor_set(v___x_5644_, 1, v___x_5633_);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v___x_5635_);
v___x_5646_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5645_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
lean_ctor_set(v___x_5648_, 1, v___x_5624_);
v___x_5649_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5650_ = l_Bool_repr___redArg(v_eta_5610_);
v___x_5651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5649_);
lean_ctor_set(v___x_5651_, 1, v___x_5650_);
v___x_5652_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5652_, 0, v___x_5651_);
lean_ctor_set_uint8(v___x_5652_, sizeof(void*)*1, v___x_5630_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5648_);
lean_ctor_set(v___x_5653_, 1, v___x_5652_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v___x_5633_);
v___x_5655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5654_);
lean_ctor_set(v___x_5655_, 1, v___x_5635_);
v___x_5656_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5655_);
lean_ctor_set(v___x_5657_, 1, v___x_5656_);
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
lean_ctor_set(v___x_5658_, 1, v___x_5624_);
v___x_5659_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5660_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5611_, v___x_5627_);
v___x_5661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5659_);
lean_ctor_set(v___x_5661_, 1, v___x_5660_);
v___x_5662_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
lean_ctor_set_uint8(v___x_5662_, sizeof(void*)*1, v___x_5630_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5658_);
lean_ctor_set(v___x_5663_, 1, v___x_5662_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5633_);
v___x_5665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
lean_ctor_set(v___x_5665_, 1, v___x_5635_);
v___x_5666_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5665_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___x_5624_);
v___x_5669_ = l_Bool_repr___redArg(v_iota_5612_);
v___x_5670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5626_);
lean_ctor_set(v___x_5670_, 1, v___x_5669_);
v___x_5671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set_uint8(v___x_5671_, sizeof(void*)*1, v___x_5630_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5668_);
lean_ctor_set(v___x_5672_, 1, v___x_5671_);
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
lean_ctor_set(v___x_5673_, 1, v___x_5633_);
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5673_);
lean_ctor_set(v___x_5674_, 1, v___x_5635_);
v___x_5675_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5674_);
lean_ctor_set(v___x_5676_, 1, v___x_5675_);
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5676_);
lean_ctor_set(v___x_5677_, 1, v___x_5624_);
v___x_5678_ = l_Bool_repr___redArg(v_proj_5613_);
v___x_5679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5626_);
lean_ctor_set(v___x_5679_, 1, v___x_5678_);
v___x_5680_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
lean_ctor_set_uint8(v___x_5680_, sizeof(void*)*1, v___x_5630_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5677_);
lean_ctor_set(v___x_5681_, 1, v___x_5680_);
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set(v___x_5682_, 1, v___x_5633_);
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
lean_ctor_set(v___x_5683_, 1, v___x_5635_);
v___x_5684_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5683_);
lean_ctor_set(v___x_5685_, 1, v___x_5684_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
lean_ctor_set(v___x_5686_, 1, v___x_5624_);
v___x_5687_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5688_ = l_Bool_repr___redArg(v_decide_5614_);
v___x_5689_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5687_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
v___x_5690_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
lean_ctor_set_uint8(v___x_5690_, sizeof(void*)*1, v___x_5630_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5686_);
lean_ctor_set(v___x_5691_, 1, v___x_5690_);
v___x_5692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
lean_ctor_set(v___x_5692_, 1, v___x_5633_);
v___x_5693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5692_);
lean_ctor_set(v___x_5693_, 1, v___x_5635_);
v___x_5694_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5693_);
lean_ctor_set(v___x_5695_, 1, v___x_5694_);
v___x_5696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5695_);
lean_ctor_set(v___x_5696_, 1, v___x_5624_);
v___x_5697_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5698_ = l_Bool_repr___redArg(v_autoUnfold_5615_);
v___x_5699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5697_);
lean_ctor_set(v___x_5699_, 1, v___x_5698_);
v___x_5700_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set_uint8(v___x_5700_, sizeof(void*)*1, v___x_5630_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5696_);
lean_ctor_set(v___x_5701_, 1, v___x_5700_);
v___x_5702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5701_);
lean_ctor_set(v___x_5702_, 1, v___x_5633_);
v___x_5703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
lean_ctor_set(v___x_5703_, 1, v___x_5635_);
v___x_5704_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5703_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
lean_ctor_set(v___x_5706_, 1, v___x_5624_);
v___x_5707_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5708_ = l_Bool_repr___redArg(v_failIfUnchanged_5616_);
v___x_5709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5707_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set_uint8(v___x_5710_, sizeof(void*)*1, v___x_5630_);
v___x_5711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5706_);
lean_ctor_set(v___x_5711_, 1, v___x_5710_);
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
lean_ctor_set(v___x_5712_, 1, v___x_5633_);
v___x_5713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set(v___x_5713_, 1, v___x_5635_);
v___x_5714_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5713_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5715_);
lean_ctor_set(v___x_5716_, 1, v___x_5624_);
v___x_5717_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5718_ = l_Bool_repr___redArg(v_unfoldPartialApp_5617_);
v___x_5719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5717_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
v___x_5720_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5720_, 0, v___x_5719_);
lean_ctor_set_uint8(v___x_5720_, sizeof(void*)*1, v___x_5630_);
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5716_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5721_);
lean_ctor_set(v___x_5722_, 1, v___x_5633_);
v___x_5723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
lean_ctor_set(v___x_5723_, 1, v___x_5635_);
v___x_5724_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5723_);
lean_ctor_set(v___x_5725_, 1, v___x_5724_);
v___x_5726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5725_);
lean_ctor_set(v___x_5726_, 1, v___x_5624_);
v___x_5727_ = l_Bool_repr___redArg(v_zetaDelta_5618_);
v___x_5728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5659_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set_uint8(v___x_5729_, sizeof(void*)*1, v___x_5630_);
v___x_5730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5726_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
lean_ctor_set(v___x_5731_, 1, v___x_5633_);
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5731_);
lean_ctor_set(v___x_5732_, 1, v___x_5635_);
v___x_5733_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5732_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
lean_ctor_set(v___x_5735_, 1, v___x_5624_);
v___x_5736_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5737_ = l_Bool_repr___redArg(v_index_5619_);
v___x_5738_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5736_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
lean_ctor_set_uint8(v___x_5739_, sizeof(void*)*1, v___x_5630_);
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5735_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5740_);
lean_ctor_set(v___x_5741_, 1, v___x_5633_);
v___x_5742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5741_);
lean_ctor_set(v___x_5742_, 1, v___x_5635_);
v___x_5743_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5742_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5744_);
lean_ctor_set(v___x_5745_, 1, v___x_5624_);
v___x_5746_ = l_Bool_repr___redArg(v_zetaUnused_5620_);
v___x_5747_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5697_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set_uint8(v___x_5748_, sizeof(void*)*1, v___x_5630_);
v___x_5749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5745_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set(v___x_5750_, 1, v___x_5633_);
v___x_5751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
lean_ctor_set(v___x_5751_, 1, v___x_5635_);
v___x_5752_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5751_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
lean_ctor_set(v___x_5754_, 1, v___x_5624_);
v___x_5755_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5756_ = l_Bool_repr___redArg(v_zetaHave_5621_);
v___x_5757_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5755_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
lean_ctor_set_uint8(v___x_5758_, sizeof(void*)*1, v___x_5630_);
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5754_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
v___x_5760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5759_);
lean_ctor_set(v___x_5760_, 1, v___x_5633_);
v___x_5761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5760_);
lean_ctor_set(v___x_5761_, 1, v___x_5635_);
v___x_5762_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___x_5761_);
lean_ctor_set(v___x_5763_, 1, v___x_5762_);
v___x_5764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5763_);
lean_ctor_set(v___x_5764_, 1, v___x_5624_);
v___x_5765_ = l_Bool_repr___redArg(v_locals_5622_);
v___x_5766_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5687_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set_uint8(v___x_5767_, sizeof(void*)*1, v___x_5630_);
v___x_5768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___x_5764_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5769_, 0, v___x_5768_);
lean_ctor_set(v___x_5769_, 1, v___x_5633_);
v___x_5770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5769_);
lean_ctor_set(v___x_5770_, 1, v___x_5635_);
v___x_5771_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5770_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5773_, 0, v___x_5772_);
lean_ctor_set(v___x_5773_, 1, v___x_5624_);
v___x_5774_ = l_Bool_repr___redArg(v_instances_5623_);
v___x_5775_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5775_, 0, v___x_5659_);
lean_ctor_set(v___x_5775_, 1, v___x_5774_);
v___x_5776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5776_, 0, v___x_5775_);
lean_ctor_set_uint8(v___x_5776_, sizeof(void*)*1, v___x_5630_);
v___x_5777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5773_);
lean_ctor_set(v___x_5777_, 1, v___x_5776_);
v___x_5778_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5779_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5780_, 0, v___x_5779_);
lean_ctor_set(v___x_5780_, 1, v___x_5777_);
v___x_5781_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5780_);
lean_ctor_set(v___x_5782_, 1, v___x_5781_);
v___x_5783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5783_, 0, v___x_5778_);
lean_ctor_set(v___x_5783_, 1, v___x_5782_);
v___x_5784_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5784_, 0, v___x_5783_);
lean_ctor_set_uint8(v___x_5784_, sizeof(void*)*1, v___x_5630_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5785_){
_start:
{
lean_object* v_res_5786_; 
v_res_5786_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5785_);
lean_dec_ref(v_x_5785_);
return v_res_5786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5787_, lean_object* v_prec_5788_){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5787_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5790_, lean_object* v_prec_5791_){
_start:
{
lean_object* v_res_5792_; 
v_res_5792_ = l_Lean_Meta_instReprConfig_repr(v_x_5790_, v_prec_5791_);
lean_dec(v_prec_5791_);
lean_dec_ref(v_x_5790_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5800_, lean_object* v_x_5801_){
_start:
{
if (lean_obj_tag(v_x_5800_) == 0)
{
lean_object* v___x_5802_; 
v___x_5802_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5802_;
}
else
{
lean_object* v_val_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5814_; 
v_val_5803_ = lean_ctor_get(v_x_5800_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v_x_5800_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5805_ = v_x_5800_;
v_isShared_5806_ = v_isSharedCheck_5814_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_val_5803_);
lean_dec(v_x_5800_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5814_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5810_; 
v___x_5807_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5808_ = l_Nat_reprFast(v_val_5803_);
if (v_isShared_5806_ == 0)
{
lean_ctor_set_tag(v___x_5805_, 3);
lean_ctor_set(v___x_5805_, 0, v___x_5808_);
v___x_5810_ = v___x_5805_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5808_);
v___x_5810_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5807_);
lean_ctor_set(v___x_5811_, 1, v___x_5810_);
v___x_5812_ = l_Repr_addAppParen(v___x_5811_, v_x_5801_);
return v___x_5812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5815_, lean_object* v_x_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5815_, v_x_5816_);
lean_dec(v_x_5816_);
return v_res_5817_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = lean_unsigned_to_nat(21u);
v___x_5831_ = lean_nat_to_int(v___x_5830_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_unsigned_to_nat(11u);
v___x_5839_ = lean_nat_to_int(v___x_5838_);
return v___x_5839_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = lean_unsigned_to_nat(23u);
v___x_5856_ = lean_nat_to_int(v___x_5855_);
return v___x_5856_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5860_ = lean_unsigned_to_nat(16u);
v___x_5861_ = lean_nat_to_int(v___x_5860_);
return v___x_5861_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5868_ = lean_unsigned_to_nat(15u);
v___x_5869_ = lean_nat_to_int(v___x_5868_);
return v___x_5869_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___x_5876_ = lean_unsigned_to_nat(17u);
v___x_5877_ = lean_nat_to_int(v___x_5876_);
return v___x_5877_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; 
v___x_5884_ = lean_unsigned_to_nat(18u);
v___x_5885_ = lean_nat_to_int(v___x_5884_);
return v___x_5885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5886_){
_start:
{
lean_object* v_maxSteps_5887_; lean_object* v_maxDischargeDepth_5888_; uint8_t v_contextual_5889_; uint8_t v_memoize_5890_; uint8_t v_singlePass_5891_; uint8_t v_zeta_5892_; uint8_t v_beta_5893_; uint8_t v_eta_5894_; uint8_t v_etaStruct_5895_; uint8_t v_iota_5896_; uint8_t v_proj_5897_; uint8_t v_decide_5898_; uint8_t v_arith_5899_; uint8_t v_autoUnfold_5900_; uint8_t v_dsimp_5901_; uint8_t v_failIfUnchanged_5902_; uint8_t v_ground_5903_; uint8_t v_unfoldPartialApp_5904_; uint8_t v_zetaDelta_5905_; uint8_t v_index_5906_; uint8_t v_implicitDefEqProofs_5907_; uint8_t v_zetaUnused_5908_; uint8_t v_catchRuntime_5909_; uint8_t v_zetaHave_5910_; uint8_t v_letToHave_5911_; uint8_t v_congrConsts_5912_; uint8_t v_bitVecOfNat_5913_; uint8_t v_warnExponents_5914_; uint8_t v_suggestions_5915_; lean_object* v_maxSuggestions_5916_; uint8_t v_locals_5917_; uint8_t v_instances_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; 
v_maxSteps_5887_ = lean_ctor_get(v_x_5886_, 0);
lean_inc(v_maxSteps_5887_);
v_maxDischargeDepth_5888_ = lean_ctor_get(v_x_5886_, 1);
lean_inc(v_maxDischargeDepth_5888_);
v_contextual_5889_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3);
v_memoize_5890_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 1);
v_singlePass_5891_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 2);
v_zeta_5892_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 3);
v_beta_5893_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 4);
v_eta_5894_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 5);
v_etaStruct_5895_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 6);
v_iota_5896_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 7);
v_proj_5897_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 8);
v_decide_5898_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 9);
v_arith_5899_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 10);
v_autoUnfold_5900_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 11);
v_dsimp_5901_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5902_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 13);
v_ground_5903_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5904_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 15);
v_zetaDelta_5905_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 16);
v_index_5906_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5907_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 18);
v_zetaUnused_5908_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 19);
v_catchRuntime_5909_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 20);
v_zetaHave_5910_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 21);
v_letToHave_5911_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 22);
v_congrConsts_5912_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5913_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 24);
v_warnExponents_5914_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 25);
v_suggestions_5915_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 26);
v_maxSuggestions_5916_ = lean_ctor_get(v_x_5886_, 2);
lean_inc(v_maxSuggestions_5916_);
v_locals_5917_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 27);
v_instances_5918_ = lean_ctor_get_uint8(v_x_5886_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5886_);
v___x_5919_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5920_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5921_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5922_ = l_Nat_reprFast(v_maxSteps_5887_);
v___x_5923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
v___x_5924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5921_);
lean_ctor_set(v___x_5924_, 1, v___x_5923_);
v___x_5925_ = 0;
v___x_5926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5926_, 0, v___x_5924_);
lean_ctor_set_uint8(v___x_5926_, sizeof(void*)*1, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5920_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
v___x_5928_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5927_);
lean_ctor_set(v___x_5929_, 1, v___x_5928_);
v___x_5930_ = lean_box(1);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5929_);
lean_ctor_set(v___x_5931_, 1, v___x_5930_);
v___x_5932_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5931_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5919_);
v___x_5935_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5936_ = l_Nat_reprFast(v_maxDischargeDepth_5888_);
v___x_5937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5936_);
v___x_5938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5935_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5925_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5934_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5928_);
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5941_);
lean_ctor_set(v___x_5942_, 1, v___x_5930_);
v___x_5943_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set(v___x_5945_, 1, v___x_5919_);
v___x_5946_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5947_ = lean_unsigned_to_nat(0u);
v___x_5948_ = l_Bool_repr___redArg(v_contextual_5889_);
v___x_5949_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5946_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set_uint8(v___x_5950_, sizeof(void*)*1, v___x_5925_);
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5945_);
lean_ctor_set(v___x_5951_, 1, v___x_5950_);
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
lean_ctor_set(v___x_5952_, 1, v___x_5928_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5952_);
lean_ctor_set(v___x_5953_, 1, v___x_5930_);
v___x_5954_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5953_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5955_);
lean_ctor_set(v___x_5956_, 1, v___x_5919_);
v___x_5957_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5958_ = l_Bool_repr___redArg(v_memoize_5890_);
v___x_5959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5957_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5960_, 0, v___x_5959_);
lean_ctor_set_uint8(v___x_5960_, sizeof(void*)*1, v___x_5925_);
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5956_);
lean_ctor_set(v___x_5961_, 1, v___x_5960_);
v___x_5962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_ctor_set(v___x_5962_, 1, v___x_5928_);
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
lean_ctor_set(v___x_5963_, 1, v___x_5930_);
v___x_5964_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5963_);
lean_ctor_set(v___x_5965_, 1, v___x_5964_);
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set(v___x_5966_, 1, v___x_5919_);
v___x_5967_ = l_Bool_repr___redArg(v_singlePass_5891_);
v___x_5968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5946_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set_uint8(v___x_5969_, sizeof(void*)*1, v___x_5925_);
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5966_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
lean_ctor_set(v___x_5971_, 1, v___x_5928_);
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
lean_ctor_set(v___x_5972_, 1, v___x_5930_);
v___x_5973_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5972_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
lean_ctor_set(v___x_5975_, 1, v___x_5919_);
v___x_5976_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5977_ = l_Bool_repr___redArg(v_zeta_5892_);
v___x_5978_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5976_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set_uint8(v___x_5979_, sizeof(void*)*1, v___x_5925_);
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5975_);
lean_ctor_set(v___x_5980_, 1, v___x_5979_);
v___x_5981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5980_);
lean_ctor_set(v___x_5981_, 1, v___x_5928_);
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5981_);
lean_ctor_set(v___x_5982_, 1, v___x_5930_);
v___x_5983_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5982_);
lean_ctor_set(v___x_5984_, 1, v___x_5983_);
v___x_5985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
lean_ctor_set(v___x_5985_, 1, v___x_5919_);
v___x_5986_ = l_Bool_repr___redArg(v_beta_5893_);
v___x_5987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5976_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set_uint8(v___x_5988_, sizeof(void*)*1, v___x_5925_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5985_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
lean_ctor_set(v___x_5990_, 1, v___x_5928_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
lean_ctor_set(v___x_5991_, 1, v___x_5930_);
v___x_5992_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5991_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set(v___x_5994_, 1, v___x_5919_);
v___x_5995_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5996_ = l_Bool_repr___redArg(v_eta_5894_);
v___x_5997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5995_);
lean_ctor_set(v___x_5997_, 1, v___x_5996_);
v___x_5998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5998_, 0, v___x_5997_);
lean_ctor_set_uint8(v___x_5998_, sizeof(void*)*1, v___x_5925_);
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5994_);
lean_ctor_set(v___x_5999_, 1, v___x_5998_);
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set(v___x_6000_, 1, v___x_5928_);
v___x_6001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set(v___x_6001_, 1, v___x_5930_);
v___x_6002_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6001_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set(v___x_6004_, 1, v___x_5919_);
v___x_6005_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_6006_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5895_, v___x_5947_);
v___x_6007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6005_);
lean_ctor_set(v___x_6007_, 1, v___x_6006_);
v___x_6008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6008_, 0, v___x_6007_);
lean_ctor_set_uint8(v___x_6008_, sizeof(void*)*1, v___x_5925_);
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6004_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set(v___x_6010_, 1, v___x_5928_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set(v___x_6011_, 1, v___x_5930_);
v___x_6012_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6011_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set(v___x_6014_, 1, v___x_5919_);
v___x_6015_ = l_Bool_repr___redArg(v_iota_5896_);
v___x_6016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_5976_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set_uint8(v___x_6017_, sizeof(void*)*1, v___x_5925_);
v___x_6018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6014_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
lean_ctor_set(v___x_6019_, 1, v___x_5928_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_5930_);
v___x_6021_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6020_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_5919_);
v___x_6024_ = l_Bool_repr___redArg(v_proj_5897_);
v___x_6025_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_5976_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set_uint8(v___x_6026_, sizeof(void*)*1, v___x_5925_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6023_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set(v___x_6028_, 1, v___x_5928_);
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set(v___x_6029_, 1, v___x_5930_);
v___x_6030_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6029_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_5919_);
v___x_6033_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6034_ = l_Bool_repr___redArg(v_decide_5898_);
v___x_6035_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6033_);
lean_ctor_set(v___x_6035_, 1, v___x_6034_);
v___x_6036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
lean_ctor_set_uint8(v___x_6036_, sizeof(void*)*1, v___x_5925_);
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6032_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_5928_);
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6038_);
lean_ctor_set(v___x_6039_, 1, v___x_5930_);
v___x_6040_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6039_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set(v___x_6042_, 1, v___x_5919_);
v___x_6043_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6044_ = l_Bool_repr___redArg(v_arith_5899_);
v___x_6045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6043_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___x_6046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6046_, 0, v___x_6045_);
lean_ctor_set_uint8(v___x_6046_, sizeof(void*)*1, v___x_5925_);
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6042_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set(v___x_6048_, 1, v___x_5928_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6048_);
lean_ctor_set(v___x_6049_, 1, v___x_5930_);
v___x_6050_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6049_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6051_);
lean_ctor_set(v___x_6052_, 1, v___x_5919_);
v___x_6053_ = l_Bool_repr___redArg(v_autoUnfold_5900_);
v___x_6054_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_5946_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set_uint8(v___x_6055_, sizeof(void*)*1, v___x_5925_);
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6052_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set(v___x_6057_, 1, v___x_5928_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
lean_ctor_set(v___x_6058_, 1, v___x_5930_);
v___x_6059_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6058_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set(v___x_6061_, 1, v___x_5919_);
v___x_6062_ = l_Bool_repr___redArg(v_dsimp_5901_);
v___x_6063_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6043_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___x_6064_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set_uint8(v___x_6064_, sizeof(void*)*1, v___x_5925_);
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6061_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
lean_ctor_set(v___x_6066_, 1, v___x_5928_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v___x_5930_);
v___x_6068_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set(v___x_6070_, 1, v___x_5919_);
v___x_6071_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6072_ = l_Bool_repr___redArg(v_failIfUnchanged_5902_);
v___x_6073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6071_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
lean_ctor_set_uint8(v___x_6074_, sizeof(void*)*1, v___x_5925_);
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6070_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set(v___x_6076_, 1, v___x_5928_);
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6076_);
lean_ctor_set(v___x_6077_, 1, v___x_5930_);
v___x_6078_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6077_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
lean_ctor_set(v___x_6080_, 1, v___x_5919_);
v___x_6081_ = l_Bool_repr___redArg(v_ground_5903_);
v___x_6082_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6033_);
lean_ctor_set(v___x_6082_, 1, v___x_6081_);
v___x_6083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set_uint8(v___x_6083_, sizeof(void*)*1, v___x_5925_);
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6080_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5928_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
lean_ctor_set(v___x_6086_, 1, v___x_5930_);
v___x_6087_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6086_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set(v___x_6089_, 1, v___x_5919_);
v___x_6090_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6091_ = l_Bool_repr___redArg(v_unfoldPartialApp_5904_);
v___x_6092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6090_);
lean_ctor_set(v___x_6092_, 1, v___x_6091_);
v___x_6093_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set_uint8(v___x_6093_, sizeof(void*)*1, v___x_5925_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6089_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set(v___x_6095_, 1, v___x_5928_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_5930_);
v___x_6097_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6096_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set(v___x_6099_, 1, v___x_5919_);
v___x_6100_ = l_Bool_repr___redArg(v_zetaDelta_5905_);
v___x_6101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6005_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set_uint8(v___x_6102_, sizeof(void*)*1, v___x_5925_);
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6099_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_5928_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_5930_);
v___x_6106_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6105_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v___x_5919_);
v___x_6109_ = l_Bool_repr___redArg(v_index_5906_);
v___x_6110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6043_);
lean_ctor_set(v___x_6110_, 1, v___x_6109_);
v___x_6111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set_uint8(v___x_6111_, sizeof(void*)*1, v___x_5925_);
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6108_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_5928_);
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set(v___x_6114_, 1, v___x_5930_);
v___x_6115_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_5919_);
v___x_6118_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6119_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5907_);
v___x_6120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6118_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set_uint8(v___x_6121_, sizeof(void*)*1, v___x_5925_);
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6117_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set(v___x_6123_, 1, v___x_5928_);
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set(v___x_6124_, 1, v___x_5930_);
v___x_6125_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6124_);
lean_ctor_set(v___x_6126_, 1, v___x_6125_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
lean_ctor_set(v___x_6127_, 1, v___x_5919_);
v___x_6128_ = l_Bool_repr___redArg(v_zetaUnused_5908_);
v___x_6129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_5946_);
lean_ctor_set(v___x_6129_, 1, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
lean_ctor_set_uint8(v___x_6130_, sizeof(void*)*1, v___x_5925_);
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6127_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5928_);
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set(v___x_6133_, 1, v___x_5930_);
v___x_6134_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6133_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set(v___x_6136_, 1, v___x_5919_);
v___x_6137_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6138_ = l_Bool_repr___redArg(v_catchRuntime_5909_);
v___x_6139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6137_);
lean_ctor_set(v___x_6139_, 1, v___x_6138_);
v___x_6140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
lean_ctor_set_uint8(v___x_6140_, sizeof(void*)*1, v___x_5925_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6136_);
lean_ctor_set(v___x_6141_, 1, v___x_6140_);
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6141_);
lean_ctor_set(v___x_6142_, 1, v___x_5928_);
v___x_6143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set(v___x_6143_, 1, v___x_5930_);
v___x_6144_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6143_);
lean_ctor_set(v___x_6145_, 1, v___x_6144_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
lean_ctor_set(v___x_6146_, 1, v___x_5919_);
v___x_6147_ = l_Bool_repr___redArg(v_zetaHave_5910_);
v___x_6148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_5921_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
v___x_6149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set_uint8(v___x_6149_, sizeof(void*)*1, v___x_5925_);
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6146_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_5928_);
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
lean_ctor_set(v___x_6152_, 1, v___x_5930_);
v___x_6153_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6152_);
lean_ctor_set(v___x_6154_, 1, v___x_6153_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set(v___x_6155_, 1, v___x_5919_);
v___x_6156_ = l_Bool_repr___redArg(v_letToHave_5911_);
v___x_6157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6005_);
lean_ctor_set(v___x_6157_, 1, v___x_6156_);
v___x_6158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
lean_ctor_set_uint8(v___x_6158_, sizeof(void*)*1, v___x_5925_);
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6155_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set(v___x_6160_, 1, v___x_5928_);
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
lean_ctor_set(v___x_6161_, 1, v___x_5930_);
v___x_6162_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6161_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
lean_ctor_set(v___x_6164_, 1, v___x_5919_);
v___x_6165_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6166_ = l_Bool_repr___redArg(v_congrConsts_5912_);
v___x_6167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6165_);
lean_ctor_set(v___x_6167_, 1, v___x_6166_);
v___x_6168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6168_, 0, v___x_6167_);
lean_ctor_set_uint8(v___x_6168_, sizeof(void*)*1, v___x_5925_);
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6164_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
lean_ctor_set(v___x_6170_, 1, v___x_5928_);
v___x_6171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
lean_ctor_set(v___x_6171_, 1, v___x_5930_);
v___x_6172_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6171_);
lean_ctor_set(v___x_6173_, 1, v___x_6172_);
v___x_6174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6173_);
lean_ctor_set(v___x_6174_, 1, v___x_5919_);
v___x_6175_ = l_Bool_repr___redArg(v_bitVecOfNat_5913_);
v___x_6176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6165_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set_uint8(v___x_6177_, sizeof(void*)*1, v___x_5925_);
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6174_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_5928_);
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6179_);
lean_ctor_set(v___x_6180_, 1, v___x_5930_);
v___x_6181_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6180_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
v___x_6183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6182_);
lean_ctor_set(v___x_6183_, 1, v___x_5919_);
v___x_6184_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6185_ = l_Bool_repr___redArg(v_warnExponents_5914_);
v___x_6186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6184_);
lean_ctor_set(v___x_6186_, 1, v___x_6185_);
v___x_6187_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set_uint8(v___x_6187_, sizeof(void*)*1, v___x_5925_);
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6183_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
lean_ctor_set(v___x_6189_, 1, v___x_5928_);
v___x_6190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6189_);
lean_ctor_set(v___x_6190_, 1, v___x_5930_);
v___x_6191_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6190_);
lean_ctor_set(v___x_6192_, 1, v___x_6191_);
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6192_);
lean_ctor_set(v___x_6193_, 1, v___x_5919_);
v___x_6194_ = l_Bool_repr___redArg(v_suggestions_5915_);
v___x_6195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6165_);
lean_ctor_set(v___x_6195_, 1, v___x_6194_);
v___x_6196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
lean_ctor_set_uint8(v___x_6196_, sizeof(void*)*1, v___x_5925_);
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6193_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___x_5928_);
v___x_6199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6198_);
lean_ctor_set(v___x_6199_, 1, v___x_5930_);
v___x_6200_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6199_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
lean_ctor_set(v___x_6202_, 1, v___x_5919_);
v___x_6203_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6204_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5916_, v___x_5947_);
v___x_6205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6205_, 0, v___x_6203_);
lean_ctor_set(v___x_6205_, 1, v___x_6204_);
v___x_6206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6206_, 0, v___x_6205_);
lean_ctor_set_uint8(v___x_6206_, sizeof(void*)*1, v___x_5925_);
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6202_);
lean_ctor_set(v___x_6207_, 1, v___x_6206_);
v___x_6208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6207_);
lean_ctor_set(v___x_6208_, 1, v___x_5928_);
v___x_6209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6208_);
lean_ctor_set(v___x_6209_, 1, v___x_5930_);
v___x_6210_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6209_);
lean_ctor_set(v___x_6211_, 1, v___x_6210_);
v___x_6212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6211_);
lean_ctor_set(v___x_6212_, 1, v___x_5919_);
v___x_6213_ = l_Bool_repr___redArg(v_locals_5917_);
v___x_6214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6033_);
lean_ctor_set(v___x_6214_, 1, v___x_6213_);
v___x_6215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6215_, 0, v___x_6214_);
lean_ctor_set_uint8(v___x_6215_, sizeof(void*)*1, v___x_5925_);
v___x_6216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6212_);
lean_ctor_set(v___x_6216_, 1, v___x_6215_);
v___x_6217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
lean_ctor_set(v___x_6217_, 1, v___x_5928_);
v___x_6218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6217_);
lean_ctor_set(v___x_6218_, 1, v___x_5930_);
v___x_6219_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6220_, 0, v___x_6218_);
lean_ctor_set(v___x_6220_, 1, v___x_6219_);
v___x_6221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6220_);
lean_ctor_set(v___x_6221_, 1, v___x_5919_);
v___x_6222_ = l_Bool_repr___redArg(v_instances_5918_);
v___x_6223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6005_);
lean_ctor_set(v___x_6223_, 1, v___x_6222_);
v___x_6224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6224_, 0, v___x_6223_);
lean_ctor_set_uint8(v___x_6224_, sizeof(void*)*1, v___x_5925_);
v___x_6225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6221_);
lean_ctor_set(v___x_6225_, 1, v___x_6224_);
v___x_6226_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6227_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6228_, 0, v___x_6227_);
lean_ctor_set(v___x_6228_, 1, v___x_6225_);
v___x_6229_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6230_, 0, v___x_6228_);
lean_ctor_set(v___x_6230_, 1, v___x_6229_);
v___x_6231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6231_, 0, v___x_6226_);
lean_ctor_set(v___x_6231_, 1, v___x_6230_);
v___x_6232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6232_, 0, v___x_6231_);
lean_ctor_set_uint8(v___x_6232_, sizeof(void*)*1, v___x_5925_);
return v___x_6232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6233_, lean_object* v_prec_6234_){
_start:
{
lean_object* v___x_6235_; 
v___x_6235_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6233_);
return v___x_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6236_, lean_object* v_prec_6237_){
_start:
{
lean_object* v_res_6238_; 
v_res_6238_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6236_, v_prec_6237_);
lean_dec(v_prec_6237_);
return v_res_6238_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6241_, lean_object* v_x_6242_){
_start:
{
if (lean_obj_tag(v_x_6242_) == 0)
{
uint8_t v___x_6243_; 
v___x_6243_ = 0;
return v___x_6243_;
}
else
{
lean_object* v_head_6244_; lean_object* v_tail_6245_; uint8_t v___x_6246_; 
v_head_6244_ = lean_ctor_get(v_x_6242_, 0);
v_tail_6245_ = lean_ctor_get(v_x_6242_, 1);
v___x_6246_ = lean_nat_dec_eq(v_a_6241_, v_head_6244_);
if (v___x_6246_ == 0)
{
v_x_6242_ = v_tail_6245_;
goto _start;
}
else
{
return v___x_6246_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6248_, lean_object* v_x_6249_){
_start:
{
uint8_t v_res_6250_; lean_object* v_r_6251_; 
v_res_6250_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6248_, v_x_6249_);
lean_dec(v_x_6249_);
lean_dec(v_a_6248_);
v_r_6251_ = lean_box(v_res_6250_);
return v_r_6251_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6252_, lean_object* v_x_6253_){
_start:
{
switch(lean_obj_tag(v_x_6252_))
{
case 0:
{
uint8_t v___x_6254_; 
v___x_6254_ = 1;
return v___x_6254_;
}
case 1:
{
lean_object* v_idxs_6255_; uint8_t v___x_6256_; 
v_idxs_6255_ = lean_ctor_get(v_x_6252_, 0);
v___x_6256_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6253_, v_idxs_6255_);
return v___x_6256_;
}
default: 
{
lean_object* v_idxs_6257_; uint8_t v___x_6258_; 
v_idxs_6257_ = lean_ctor_get(v_x_6252_, 0);
v___x_6258_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6253_, v_idxs_6257_);
if (v___x_6258_ == 0)
{
uint8_t v___x_6259_; 
v___x_6259_ = 1;
return v___x_6259_;
}
else
{
uint8_t v___x_6260_; 
v___x_6260_ = 0;
return v___x_6260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6261_, lean_object* v_x_6262_){
_start:
{
uint8_t v_res_6263_; lean_object* v_r_6264_; 
v_res_6263_ = l_Lean_Meta_Occurrences_contains(v_x_6261_, v_x_6262_);
lean_dec(v_x_6262_);
lean_dec(v_x_6261_);
v_r_6264_ = lean_box(v_res_6263_);
return v_r_6264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6265_){
_start:
{
if (lean_obj_tag(v_x_6265_) == 0)
{
uint8_t v___x_6266_; 
v___x_6266_ = 1;
return v___x_6266_;
}
else
{
uint8_t v___x_6267_; 
v___x_6267_ = 0;
return v___x_6267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6268_){
_start:
{
uint8_t v_res_6269_; lean_object* v_r_6270_; 
v_res_6269_ = l_Lean_Meta_Occurrences_isAll(v_x_6268_);
lean_dec(v_x_6268_);
v_r_6270_ = lean_box(v_res_6269_);
return v_r_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(uint8_t v_x_6271_){
_start:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6272_ = lean_box(v_x_6271_);
v___x_6273_ = lean_obj_tag_nat(v___x_6272_);
lean_dec(v___x_6272_);
return v___x_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl___boxed(lean_object* v_x_6274_){
_start:
{
uint8_t v_x_4__boxed_6275_; lean_object* v_res_6276_; 
v_x_4__boxed_6275_ = lean_unbox(v_x_6274_);
v_res_6276_ = l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(v_x_4__boxed_6275_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6277_){
_start:
{
lean_inc(v_k_6277_);
return v_k_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6278_){
_start:
{
lean_object* v_res_6279_; 
v_res_6279_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6278_);
lean_dec(v_k_6278_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6280_, lean_object* v_ctorIdx_6281_, uint8_t v_t_6282_, lean_object* v_h_6283_, lean_object* v_k_6284_){
_start:
{
lean_inc(v_k_6284_);
return v_k_6284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6285_, lean_object* v_ctorIdx_6286_, lean_object* v_t_6287_, lean_object* v_h_6288_, lean_object* v_k_6289_){
_start:
{
uint8_t v_t_boxed_6290_; lean_object* v_res_6291_; 
v_t_boxed_6290_ = lean_unbox(v_t_6287_);
v_res_6291_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6285_, v_ctorIdx_6286_, v_t_boxed_6290_, v_h_6288_, v_k_6289_);
lean_dec(v_k_6289_);
lean_dec(v_ctorIdx_6286_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6292_){
_start:
{
lean_inc(v_nonDependentFirst_6292_);
return v_nonDependentFirst_6292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6293_){
_start:
{
lean_object* v_res_6294_; 
v_res_6294_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6293_);
lean_dec(v_nonDependentFirst_6293_);
return v_res_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6295_, uint8_t v_t_6296_, lean_object* v_h_6297_, lean_object* v_nonDependentFirst_6298_){
_start:
{
lean_inc(v_nonDependentFirst_6298_);
return v_nonDependentFirst_6298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6299_, lean_object* v_t_6300_, lean_object* v_h_6301_, lean_object* v_nonDependentFirst_6302_){
_start:
{
uint8_t v_t_boxed_6303_; lean_object* v_res_6304_; 
v_t_boxed_6303_ = lean_unbox(v_t_6300_);
v_res_6304_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6299_, v_t_boxed_6303_, v_h_6301_, v_nonDependentFirst_6302_);
lean_dec(v_nonDependentFirst_6302_);
return v_res_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6305_){
_start:
{
lean_inc(v_nonDependentOnly_6305_);
return v_nonDependentOnly_6305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6306_){
_start:
{
lean_object* v_res_6307_; 
v_res_6307_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6306_);
lean_dec(v_nonDependentOnly_6306_);
return v_res_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6308_, uint8_t v_t_6309_, lean_object* v_h_6310_, lean_object* v_nonDependentOnly_6311_){
_start:
{
lean_inc(v_nonDependentOnly_6311_);
return v_nonDependentOnly_6311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6312_, lean_object* v_t_6313_, lean_object* v_h_6314_, lean_object* v_nonDependentOnly_6315_){
_start:
{
uint8_t v_t_boxed_6316_; lean_object* v_res_6317_; 
v_t_boxed_6316_ = lean_unbox(v_t_6313_);
v_res_6317_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6312_, v_t_boxed_6316_, v_h_6314_, v_nonDependentOnly_6315_);
lean_dec(v_nonDependentOnly_6315_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6318_){
_start:
{
lean_inc(v_all_6318_);
return v_all_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6319_){
_start:
{
lean_object* v_res_6320_; 
v_res_6320_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6319_);
lean_dec(v_all_6319_);
return v_res_6320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6321_, uint8_t v_t_6322_, lean_object* v_h_6323_, lean_object* v_all_6324_){
_start:
{
lean_inc(v_all_6324_);
return v_all_6324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6325_, lean_object* v_t_6326_, lean_object* v_h_6327_, lean_object* v_all_6328_){
_start:
{
uint8_t v_t_boxed_6329_; lean_object* v_res_6330_; 
v_t_boxed_6329_ = lean_unbox(v_t_6326_);
v_res_6330_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6325_, v_t_boxed_6329_, v_h_6327_, v_all_6328_);
lean_dec(v_all_6328_);
return v_res_6330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6344_){
_start:
{
lean_object* v___x_6345_; uint8_t v___x_6346_; 
v___x_6345_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6344_);
v___x_6346_ = l_Lean_Syntax_isOfKind(v_c_6344_, v___x_6345_);
if (v___x_6346_ == 0)
{
lean_object* v___x_6347_; uint8_t v___x_6348_; 
v___x_6347_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6344_);
v___x_6348_ = l_Lean_Syntax_isOfKind(v_c_6344_, v___x_6347_);
if (v___x_6348_ == 0)
{
lean_object* v___x_6349_; uint8_t v___x_6350_; 
v___x_6349_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6344_);
v___x_6350_ = l_Lean_Syntax_isOfKind(v_c_6344_, v___x_6349_);
if (v___x_6350_ == 0)
{
lean_object* v___x_6351_; 
lean_dec(v_c_6344_);
v___x_6351_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6351_;
}
else
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6352_ = lean_unsigned_to_nat(1u);
v___x_6353_ = lean_mk_empty_array_with_capacity(v___x_6352_);
v___x_6354_ = lean_array_push(v___x_6353_, v_c_6344_);
return v___x_6354_;
}
}
else
{
lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6355_ = lean_unsigned_to_nat(0u);
v___x_6356_ = l_Lean_Syntax_getArg(v_c_6344_, v___x_6355_);
lean_dec(v_c_6344_);
v___x_6357_ = l_Lean_Syntax_getArgs(v___x_6356_);
lean_dec(v___x_6356_);
return v___x_6357_;
}
}
else
{
lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; uint8_t v___x_6362_; 
v___x_6358_ = l_Lean_Syntax_getArgs(v_c_6344_);
lean_dec(v_c_6344_);
v___x_6359_ = lean_unsigned_to_nat(0u);
v___x_6360_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6361_ = lean_array_get_size(v___x_6358_);
v___x_6362_ = lean_nat_dec_lt(v___x_6359_, v___x_6361_);
if (v___x_6362_ == 0)
{
lean_dec_ref(v___x_6358_);
return v___x_6360_;
}
else
{
size_t v___x_6363_; size_t v___x_6364_; lean_object* v___x_6365_; 
v___x_6363_ = ((size_t)0ULL);
v___x_6364_ = lean_usize_of_nat(v___x_6361_);
v___x_6365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6358_, v___x_6363_, v___x_6364_, v___x_6360_);
lean_dec_ref(v___x_6358_);
return v___x_6365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6366_, size_t v_i_6367_, size_t v_stop_6368_, lean_object* v_b_6369_){
_start:
{
uint8_t v___x_6370_; 
v___x_6370_ = lean_usize_dec_eq(v_i_6367_, v_stop_6368_);
if (v___x_6370_ == 0)
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; size_t v___x_6374_; size_t v___x_6375_; 
v___x_6371_ = lean_array_uget_borrowed(v_as_6366_, v_i_6367_);
lean_inc(v___x_6371_);
v___x_6372_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6371_);
v___x_6373_ = l_Array_append___redArg(v_b_6369_, v___x_6372_);
lean_dec_ref(v___x_6372_);
v___x_6374_ = ((size_t)1ULL);
v___x_6375_ = lean_usize_add(v_i_6367_, v___x_6374_);
v_i_6367_ = v___x_6375_;
v_b_6369_ = v___x_6373_;
goto _start;
}
else
{
return v_b_6369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6377_, lean_object* v_i_6378_, lean_object* v_stop_6379_, lean_object* v_b_6380_){
_start:
{
size_t v_i_boxed_6381_; size_t v_stop_boxed_6382_; lean_object* v_res_6383_; 
v_i_boxed_6381_ = lean_unbox_usize(v_i_6378_);
lean_dec(v_i_6378_);
v_stop_boxed_6382_ = lean_unbox_usize(v_stop_6379_);
lean_dec(v_stop_6379_);
v_res_6383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6377_, v_i_boxed_6381_, v_stop_boxed_6382_, v_b_6380_);
lean_dec_ref(v_as_6377_);
return v_res_6383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6384_){
_start:
{
lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; 
v___x_6385_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6386_ = lean_box(2);
v___x_6387_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6388_, 0, v___x_6386_);
lean_ctor_set(v___x_6388_, 1, v___x_6387_);
lean_ctor_set(v___x_6388_, 2, v_items_6384_);
v___x_6389_ = l_Lean_Syntax_node1(v___x_6386_, v___x_6385_, v___x_6388_);
return v___x_6389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6390_, lean_object* v_cfg_x27_6391_){
_start:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6392_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6390_);
v___x_6393_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6391_);
v___x_6394_ = l_Array_append___redArg(v___x_6392_, v___x_6393_);
lean_dec_ref(v___x_6393_);
v___x_6395_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6394_);
return v___x_6395_;
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
