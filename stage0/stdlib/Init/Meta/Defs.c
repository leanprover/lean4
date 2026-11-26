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
lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f(lean_object* v_stx_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = l_Lean_Syntax_getHeadInfo(v_stx_1878_);
v___x_1880_ = l_Lean_SourceInfo_getLeading_x3f(v___x_1879_);
lean_dec(v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f___boxed(lean_object* v_stx_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Syntax_getLeading_x3f(v_stx_1881_);
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
uint8_t v___x_1884__boxed_2310_; uint8_t v_res_2311_; lean_object* v_r_2312_; 
v___x_1884__boxed_2310_ = lean_unbox(v___x_2308_);
v_res_2311_ = l_Lean_expandMacros___lam__0(v___x_1884__boxed_2310_, v_k_2309_);
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
lean_object* v_info_2318_; lean_object* v_kind_2319_; lean_object* v_args_2320_; lean_object* v___x_2321_; lean_object* v_methods_2323_; lean_object* v_quotContext_2324_; lean_object* v_currMacroScope_2325_; lean_object* v_currRecDepth_2326_; lean_object* v_maxRecDepth_2327_; lean_object* v_ref_2328_; lean_object* v___y_2329_; uint8_t v___x_2356_; 
v_info_2318_ = lean_ctor_get(v_stx_2314_, 0);
v_kind_2319_ = lean_ctor_get(v_stx_2314_, 1);
v_args_2320_ = lean_ctor_get(v_stx_2314_, 2);
lean_inc(v_kind_2319_);
v___x_2321_ = lean_apply_1(v_p_2315_, v_kind_2319_);
v___x_2356_ = lean_unbox(v___x_2321_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v_a_2316_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_stx_2314_);
lean_ctor_set(v___x_2357_, 1, v_a_2317_);
return v___x_2357_;
}
else
{
lean_object* v_methods_2358_; lean_object* v_quotContext_2359_; lean_object* v_currMacroScope_2360_; lean_object* v_currRecDepth_2361_; lean_object* v_maxRecDepth_2362_; lean_object* v_ref_2363_; lean_object* v_ref_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_methods_2358_ = lean_ctor_get(v_a_2316_, 0);
lean_inc_n(v_methods_2358_, 2);
v_quotContext_2359_ = lean_ctor_get(v_a_2316_, 1);
lean_inc_n(v_quotContext_2359_, 2);
v_currMacroScope_2360_ = lean_ctor_get(v_a_2316_, 2);
lean_inc_n(v_currMacroScope_2360_, 2);
v_currRecDepth_2361_ = lean_ctor_get(v_a_2316_, 3);
lean_inc_n(v_currRecDepth_2361_, 2);
v_maxRecDepth_2362_ = lean_ctor_get(v_a_2316_, 4);
lean_inc_n(v_maxRecDepth_2362_, 2);
v_ref_2363_ = lean_ctor_get(v_a_2316_, 5);
lean_inc(v_ref_2363_);
lean_dec_ref(v_a_2316_);
v_ref_2364_ = l_Lean_replaceRef(v_stx_2314_, v_ref_2363_);
lean_dec(v_ref_2363_);
lean_inc(v_ref_2364_);
v___x_2365_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2365_, 0, v_methods_2358_);
lean_ctor_set(v___x_2365_, 1, v_quotContext_2359_);
lean_ctor_set(v___x_2365_, 2, v_currMacroScope_2360_);
lean_ctor_set(v___x_2365_, 3, v_currRecDepth_2361_);
lean_ctor_set(v___x_2365_, 4, v_maxRecDepth_2362_);
lean_ctor_set(v___x_2365_, 5, v_ref_2364_);
lean_inc_ref(v_stx_2314_);
v___x_2366_ = l_Lean_Macro_expandMacro_x3f(v_stx_2314_, v___x_2365_, v_a_2317_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
if (lean_obj_tag(v_a_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref_known(v___x_2365_, 6);
v_a_2368_ = lean_ctor_get(v___x_2366_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v___x_2366_, 0);
lean_dec(v_unused_2381_);
v___x_2370_ = v___x_2366_;
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2366_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_nat_dec_eq(v_maxRecDepth_2362_, v___x_2372_);
if (v___x_2373_ == 0)
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_nat_dec_eq(v_currRecDepth_2361_, v_maxRecDepth_2362_);
if (v___x_2374_ == 0)
{
lean_inc_ref(v_args_2320_);
lean_inc(v_kind_2319_);
lean_inc(v_info_2318_);
lean_del_object(v___x_2370_);
lean_dec_ref_known(v_stx_2314_, 3);
v_methods_2323_ = v_methods_2358_;
v_quotContext_2324_ = v_quotContext_2359_;
v_currMacroScope_2325_ = v_currMacroScope_2360_;
v_currRecDepth_2326_ = v_currRecDepth_2361_;
v_maxRecDepth_2327_ = v_maxRecDepth_2362_;
v_ref_2328_ = v_ref_2364_;
v___y_2329_ = v_a_2368_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_dec(v_ref_2364_);
lean_dec(v_maxRecDepth_2362_);
lean_dec(v_currRecDepth_2361_);
lean_dec(v_currMacroScope_2360_);
lean_dec(v_quotContext_2359_);
lean_dec(v_methods_2358_);
v___x_2375_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_stx_2314_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 1);
lean_ctor_set(v___x_2370_, 0, v___x_2376_);
v___x_2378_ = v___x_2370_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_a_2368_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_inc_ref(v_args_2320_);
lean_inc(v_kind_2319_);
lean_inc(v_info_2318_);
lean_del_object(v___x_2370_);
lean_dec_ref_known(v_stx_2314_, 3);
v_methods_2323_ = v_methods_2358_;
v_quotContext_2324_ = v_quotContext_2359_;
v_currMacroScope_2325_ = v_currMacroScope_2360_;
v_currRecDepth_2326_ = v_currRecDepth_2361_;
v_maxRecDepth_2327_ = v_maxRecDepth_2362_;
v_ref_2328_ = v_ref_2364_;
v___y_2329_ = v_a_2368_;
goto v___jp_2322_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v_val_2383_; lean_object* v___f_2384_; 
lean_inc_ref(v_a_2367_);
lean_dec(v_ref_2364_);
lean_dec(v_maxRecDepth_2362_);
lean_dec(v_currRecDepth_2361_);
lean_dec(v_currMacroScope_2360_);
lean_dec(v_quotContext_2359_);
lean_dec(v_methods_2358_);
lean_dec_ref_known(v_stx_2314_, 3);
v_a_2382_ = lean_ctor_get(v___x_2366_, 1);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2366_, 2);
v_val_2383_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_val_2383_);
lean_dec_ref_known(v_a_2367_, 1);
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2384_, 0, v___x_2321_);
v_stx_2314_ = v_val_2383_;
v_p_2315_ = v___f_2384_;
v_a_2316_ = v___x_2365_;
v_a_2317_ = v_a_2382_;
goto _start;
}
}
else
{
lean_object* v_a_2386_; lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref_known(v___x_2365_, 6);
lean_dec(v_ref_2364_);
lean_dec(v_maxRecDepth_2362_);
lean_dec(v_currRecDepth_2361_);
lean_dec(v_currMacroScope_2360_);
lean_dec(v_quotContext_2359_);
lean_dec(v_methods_2358_);
lean_dec_ref_known(v_stx_2314_, 3);
v_a_2386_ = lean_ctor_get(v___x_2366_, 0);
v_a_2387_ = lean_ctor_get(v___x_2366_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2366_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_inc(v_a_2386_);
lean_dec(v___x_2366_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2386_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
v___jp_2322_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; size_t v_sz_2333_; size_t v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_currRecDepth_2326_, v___x_2330_);
lean_dec(v_currRecDepth_2326_);
v___x_2332_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2332_, 0, v_methods_2323_);
lean_ctor_set(v___x_2332_, 1, v_quotContext_2324_);
lean_ctor_set(v___x_2332_, 2, v_currMacroScope_2325_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
lean_ctor_set(v___x_2332_, 4, v_maxRecDepth_2327_);
lean_ctor_set(v___x_2332_, 5, v_ref_2328_);
v_sz_2333_ = lean_array_size(v_args_2320_);
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_unbox(v___x_2321_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2335_, v_sz_2333_, v___x_2334_, v_args_2320_, v___x_2332_, v___y_2329_);
lean_dec_ref_known(v___x_2332_, 6);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2346_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_a_2338_ = lean_ctor_get(v___x_2336_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2340_ = v___x_2336_;
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2342_, 0, v_info_2318_);
lean_ctor_set(v___x_2342_, 1, v_kind_2319_);
lean_ctor_set(v___x_2342_, 2, v_a_2337_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2342_);
v___x_2344_ = v___x_2340_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_a_2338_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_kind_2319_);
lean_dec(v_info_2318_);
v_a_2347_ = lean_ctor_get(v___x_2336_, 0);
v_a_2348_ = lean_ctor_get(v___x_2336_, 1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2336_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_inc(v_a_2347_);
lean_dec(v___x_2336_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2347_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
else
{
lean_object* v___x_2395_; 
lean_dec_ref(v_a_2316_);
lean_dec_ref(v_p_2315_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_stx_2314_);
lean_ctor_set(v___x_2395_, 1, v_a_2317_);
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2396_, size_t v_sz_2397_, size_t v_i_2398_, lean_object* v_bs_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = lean_usize_dec_lt(v_i_2398_, v_sz_2397_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v_bs_2399_);
lean_ctor_set(v___x_2403_, 1, v___y_2401_);
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v_v_2406_; lean_object* v___x_2407_; 
v___x_2404_ = lean_box(v___x_2396_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2405_, 0, v___x_2404_);
v_v_2406_ = lean_array_uget_borrowed(v_bs_2399_, v_i_2398_);
lean_inc_ref(v___y_2400_);
lean_inc(v_v_2406_);
v___x_2407_ = l_Lean_expandMacros(v_v_2406_, v___f_2405_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v_bs_x27_2411_; size_t v___x_2412_; size_t v___x_2413_; lean_object* v___x_2414_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
v_a_2409_ = lean_ctor_get(v___x_2407_, 1);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2407_, 2);
v___x_2410_ = lean_unsigned_to_nat(0u);
v_bs_x27_2411_ = lean_array_uset(v_bs_2399_, v_i_2398_, v___x_2410_);
v___x_2412_ = ((size_t)1ULL);
v___x_2413_ = lean_usize_add(v_i_2398_, v___x_2412_);
v___x_2414_ = lean_array_uset(v_bs_x27_2411_, v_i_2398_, v_a_2408_);
v_i_2398_ = v___x_2413_;
v_bs_2399_ = v___x_2414_;
v___y_2401_ = v_a_2409_;
goto _start;
}
else
{
lean_object* v_a_2416_; lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref(v_bs_2399_);
v_a_2416_ = lean_ctor_get(v___x_2407_, 0);
v_a_2417_ = lean_ctor_get(v___x_2407_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2407_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_inc(v_a_2416_);
lean_dec(v___x_2407_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2425_, lean_object* v_sz_2426_, lean_object* v_i_2427_, lean_object* v_bs_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_1903__boxed_2431_; size_t v_sz_boxed_2432_; size_t v_i_boxed_2433_; lean_object* v_res_2434_; 
v___x_1903__boxed_2431_ = lean_unbox(v___x_2425_);
v_sz_boxed_2432_ = lean_unbox_usize(v_sz_2426_);
lean_dec(v_sz_2426_);
v_i_boxed_2433_ = lean_unbox_usize(v_i_2427_);
lean_dec(v_i_2427_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1903__boxed_2431_, v_sz_boxed_2432_, v_i_boxed_2433_, v_bs_2428_, v___y_2429_, v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2435_, lean_object* v_val_2436_, uint8_t v_canonical_2437_){
_start:
{
lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2438_ = l_Lean_SourceInfo_fromRef(v_src_2435_, v_canonical_2437_);
v___x_2439_ = 1;
lean_inc(v_val_2436_);
v___x_2440_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2436_, v___x_2439_);
v___x_2441_ = lean_unsigned_to_nat(0u);
v___x_2442_ = lean_string_utf8_byte_size(v___x_2440_);
v___x_2443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2440_);
lean_ctor_set(v___x_2443_, 1, v___x_2441_);
lean_ctor_set(v___x_2443_, 2, v___x_2442_);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2438_);
lean_ctor_set(v___x_2445_, 1, v___x_2443_);
lean_ctor_set(v___x_2445_, 2, v_val_2436_);
lean_ctor_set(v___x_2445_, 3, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2446_, lean_object* v_val_2447_, lean_object* v_canonical_2448_){
_start:
{
uint8_t v_canonical_boxed_2449_; lean_object* v_res_2450_; 
v_canonical_boxed_2449_ = lean_unbox(v_canonical_2448_);
v_res_2450_ = l_Lean_mkIdentFrom(v_src_2446_, v_val_2447_, v_canonical_boxed_2449_);
lean_dec(v_src_2446_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2466_, lean_object* v_text_2467_, uint8_t v_canonical_2468_){
_start:
{
lean_object* v_info_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_body_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_info_2469_ = l_Lean_SourceInfo_fromRef(v_src_2466_, v_canonical_2468_);
v___x_2470_ = lean_box(2);
v___x_2471_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2469_, 2);
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_info_2469_);
lean_ctor_set(v___x_2472_, 1, v_text_2467_);
v___x_2473_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_info_2469_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_unsigned_to_nat(2u);
v___x_2476_ = lean_mk_empty_array_with_capacity(v___x_2475_);
lean_inc_ref(v___x_2476_);
v___x_2477_ = lean_array_push(v___x_2476_, v___x_2472_);
v___x_2478_ = lean_array_push(v___x_2477_, v___x_2474_);
v_body_2479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2479_, 0, v___x_2470_);
lean_ctor_set(v_body_2479_, 1, v___x_2471_);
lean_ctor_set(v_body_2479_, 2, v___x_2478_);
v___x_2480_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2481_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_info_2469_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = lean_array_push(v___x_2476_, v___x_2482_);
v___x_2484_ = lean_array_push(v___x_2483_, v_body_2479_);
v___x_2485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2470_);
lean_ctor_set(v___x_2485_, 1, v___x_2480_);
lean_ctor_set(v___x_2485_, 2, v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2486_, lean_object* v_text_2487_, lean_object* v_canonical_2488_){
_start:
{
uint8_t v_canonical_boxed_2489_; lean_object* v_res_2490_; 
v_canonical_boxed_2489_ = lean_unbox(v_canonical_2488_);
v_res_2490_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2486_, v_text_2487_, v_canonical_boxed_2489_);
lean_dec(v_src_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2491_){
_start:
{
lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = lean_box(0);
v___x_2493_ = 0;
v___x_2494_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2492_, v_text_2491_, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2495_, uint8_t v_canonical_2496_, lean_object* v_toPure_2497_, lean_object* v_____do__lift_2498_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = l_Lean_mkIdentFrom(v_____do__lift_2498_, v_val_2495_, v_canonical_2496_);
v___x_2500_ = lean_apply_2(v_toPure_2497_, lean_box(0), v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2501_, lean_object* v_canonical_2502_, lean_object* v_toPure_2503_, lean_object* v_____do__lift_2504_){
_start:
{
uint8_t v_canonical_boxed_2505_; lean_object* v_res_2506_; 
v_canonical_boxed_2505_ = lean_unbox(v_canonical_2502_);
v_res_2506_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2501_, v_canonical_boxed_2505_, v_toPure_2503_, v_____do__lift_2504_);
lean_dec(v_____do__lift_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_val_2509_, uint8_t v_canonical_2510_){
_start:
{
lean_object* v_toApplicative_2511_; lean_object* v_toBind_2512_; lean_object* v_getRef_2513_; lean_object* v_toPure_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; 
v_toApplicative_2511_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc_ref(v_toApplicative_2511_);
v_toBind_2512_ = lean_ctor_get(v_inst_2507_, 1);
lean_inc(v_toBind_2512_);
lean_dec_ref(v_inst_2507_);
v_getRef_2513_ = lean_ctor_get(v_inst_2508_, 0);
lean_inc(v_getRef_2513_);
lean_dec_ref(v_inst_2508_);
v_toPure_2514_ = lean_ctor_get(v_toApplicative_2511_, 1);
lean_inc(v_toPure_2514_);
lean_dec_ref(v_toApplicative_2511_);
v___x_2515_ = lean_box(v_canonical_2510_);
v___f_2516_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2516_, 0, v_val_2509_);
lean_closure_set(v___f_2516_, 1, v___x_2515_);
lean_closure_set(v___f_2516_, 2, v_toPure_2514_);
v___x_2517_ = lean_apply_4(v_toBind_2512_, lean_box(0), lean_box(0), v_getRef_2513_, v___f_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_val_2520_, lean_object* v_canonical_2521_){
_start:
{
uint8_t v_canonical_boxed_2522_; lean_object* v_res_2523_; 
v_canonical_boxed_2522_ = lean_unbox(v_canonical_2521_);
v_res_2523_ = l_Lean_mkIdentFromRef___redArg(v_inst_2518_, v_inst_2519_, v_val_2520_, v_canonical_boxed_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2524_, lean_object* v_inst_2525_, lean_object* v_inst_2526_, lean_object* v_val_2527_, uint8_t v_canonical_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_mkIdentFromRef___redArg(v_inst_2525_, v_inst_2526_, v_val_2527_, v_canonical_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_val_2533_, lean_object* v_canonical_2534_){
_start:
{
uint8_t v_canonical_boxed_2535_; lean_object* v_res_2536_; 
v_canonical_boxed_2535_ = lean_unbox(v_canonical_2534_);
v_res_2536_ = l_Lean_mkIdentFromRef(v_m_2530_, v_inst_2531_, v_inst_2532_, v_val_2533_, v_canonical_boxed_2535_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2540_, lean_object* v_c_2541_, uint8_t v_canonical_2542_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_id_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2543_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2544_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2541_);
v_id_2545_ = l_Lean_addMacroScope(v___x_2543_, v_c_2541_, v___x_2544_);
v___x_2546_ = l_Lean_SourceInfo_fromRef(v_src_2540_, v_canonical_2542_);
v___x_2547_ = 1;
lean_inc(v_id_2545_);
v___x_2548_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2545_, v___x_2547_);
v___x_2549_ = lean_string_utf8_byte_size(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2544_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_c_2541_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___x_2551_);
v___x_2554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2546_);
lean_ctor_set(v___x_2554_, 1, v___x_2550_);
lean_ctor_set(v___x_2554_, 2, v_id_2545_);
lean_ctor_set(v___x_2554_, 3, v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2555_, lean_object* v_c_2556_, lean_object* v_canonical_2557_){
_start:
{
uint8_t v_canonical_boxed_2558_; lean_object* v_res_2559_; 
v_canonical_boxed_2558_ = lean_unbox(v_canonical_2557_);
v_res_2559_ = l_Lean_mkCIdentFrom(v_src_2555_, v_c_2556_, v_canonical_boxed_2558_);
lean_dec(v_src_2555_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2560_, uint8_t v_canonical_2561_, lean_object* v_toPure_2562_, lean_object* v_____do__lift_2563_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = l_Lean_mkCIdentFrom(v_____do__lift_2563_, v_c_2560_, v_canonical_2561_);
v___x_2565_ = lean_apply_2(v_toPure_2562_, lean_box(0), v___x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2566_, lean_object* v_canonical_2567_, lean_object* v_toPure_2568_, lean_object* v_____do__lift_2569_){
_start:
{
uint8_t v_canonical_boxed_2570_; lean_object* v_res_2571_; 
v_canonical_boxed_2570_ = lean_unbox(v_canonical_2567_);
v_res_2571_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2566_, v_canonical_boxed_2570_, v_toPure_2568_, v_____do__lift_2569_);
lean_dec(v_____do__lift_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_c_2574_, uint8_t v_canonical_2575_){
_start:
{
lean_object* v_toApplicative_2576_; lean_object* v_toBind_2577_; lean_object* v_getRef_2578_; lean_object* v_toPure_2579_; lean_object* v___x_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; 
v_toApplicative_2576_ = lean_ctor_get(v_inst_2572_, 0);
lean_inc_ref(v_toApplicative_2576_);
v_toBind_2577_ = lean_ctor_get(v_inst_2572_, 1);
lean_inc(v_toBind_2577_);
lean_dec_ref(v_inst_2572_);
v_getRef_2578_ = lean_ctor_get(v_inst_2573_, 0);
lean_inc(v_getRef_2578_);
lean_dec_ref(v_inst_2573_);
v_toPure_2579_ = lean_ctor_get(v_toApplicative_2576_, 1);
lean_inc(v_toPure_2579_);
lean_dec_ref(v_toApplicative_2576_);
v___x_2580_ = lean_box(v_canonical_2575_);
v___f_2581_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2581_, 0, v_c_2574_);
lean_closure_set(v___f_2581_, 1, v___x_2580_);
lean_closure_set(v___f_2581_, 2, v_toPure_2579_);
v___x_2582_ = lean_apply_4(v_toBind_2577_, lean_box(0), lean_box(0), v_getRef_2578_, v___f_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_c_2585_, lean_object* v_canonical_2586_){
_start:
{
uint8_t v_canonical_boxed_2587_; lean_object* v_res_2588_; 
v_canonical_boxed_2587_ = lean_unbox(v_canonical_2586_);
v_res_2588_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2583_, v_inst_2584_, v_c_2585_, v_canonical_boxed_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_c_2592_, uint8_t v_canonical_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2590_, v_inst_2591_, v_c_2592_, v_canonical_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_c_2598_, lean_object* v_canonical_2599_){
_start:
{
uint8_t v_canonical_boxed_2600_; lean_object* v_res_2601_; 
v_canonical_boxed_2600_ = lean_unbox(v_canonical_2599_);
v_res_2601_ = l_Lean_mkCIdentFromRef(v_m_2595_, v_inst_2596_, v_inst_2597_, v_c_2598_, v_canonical_boxed_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2602_){
_start:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = 0;
v___x_2605_ = l_Lean_mkCIdentFrom(v___x_2603_, v_c_2602_, v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2606_){
_start:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2607_ = lean_box(2);
v___x_2608_ = 1;
lean_inc(v_val_2606_);
v___x_2609_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2606_, v___x_2608_);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_string_utf8_byte_size(v___x_2609_);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2609_);
lean_ctor_set(v___x_2612_, 1, v___x_2610_);
lean_ctor_set(v___x_2612_, 2, v___x_2611_);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2607_);
lean_ctor_set(v___x_2614_, 1, v___x_2612_);
lean_ctor_set(v___x_2614_, 2, v_val_2606_);
lean_ctor_set(v___x_2614_, 3, v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2618_){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2620_ = lean_box(2);
v___x_2621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___x_2619_);
lean_ctor_set(v___x_2621_, 2, v_args_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2622_, lean_object* v_as_2623_, size_t v_sz_2624_, size_t v_i_2625_, lean_object* v_b_2626_){
_start:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_usize_dec_lt(v_i_2625_, v_sz_2624_);
if (v___x_2627_ == 0)
{
lean_dec(v_sep_2622_);
return v_b_2626_;
}
else
{
lean_object* v_fst_2628_; lean_object* v_snd_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2649_; 
v_fst_2628_ = lean_ctor_get(v_b_2626_, 0);
v_snd_2629_ = lean_ctor_get(v_b_2626_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_b_2626_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2631_ = v_b_2626_;
v_isShared_2632_ = v_isSharedCheck_2649_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_snd_2629_);
lean_inc(v_fst_2628_);
lean_dec(v_b_2626_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2649_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_r_2634_; lean_object* v_i_2643_; lean_object* v_a_2644_; uint8_t v___x_2645_; 
v_i_2643_ = lean_unsigned_to_nat(0u);
v_a_2644_ = lean_array_uget_borrowed(v_as_2623_, v_i_2625_);
v___x_2645_ = lean_nat_dec_lt(v_i_2643_, v_fst_2628_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_inc(v_a_2644_);
v___x_2646_ = lean_array_push(v_snd_2629_, v_a_2644_);
v_r_2634_ = v___x_2646_;
goto v___jp_2633_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_inc(v_sep_2622_);
v___x_2647_ = lean_array_push(v_snd_2629_, v_sep_2622_);
lean_inc(v_a_2644_);
v___x_2648_ = lean_array_push(v___x_2647_, v_a_2644_);
v_r_2634_ = v___x_2648_;
goto v___jp_2633_;
}
v___jp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = lean_nat_add(v_fst_2628_, v___x_2635_);
lean_dec(v_fst_2628_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v_r_2634_);
lean_ctor_set(v___x_2631_, 0, v___x_2636_);
v___x_2638_ = v___x_2631_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_r_2634_);
v___x_2638_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
size_t v___x_2639_; size_t v___x_2640_; 
v___x_2639_ = ((size_t)1ULL);
v___x_2640_ = lean_usize_add(v_i_2625_, v___x_2639_);
v_i_2625_ = v___x_2640_;
v_b_2626_ = v___x_2638_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2650_, lean_object* v_as_2651_, lean_object* v_sz_2652_, lean_object* v_i_2653_, lean_object* v_b_2654_){
_start:
{
size_t v_sz_boxed_2655_; size_t v_i_boxed_2656_; lean_object* v_res_2657_; 
v_sz_boxed_2655_ = lean_unbox_usize(v_sz_2652_);
lean_dec(v_sz_2652_);
v_i_boxed_2656_ = lean_unbox_usize(v_i_2653_);
lean_dec(v_i_2653_);
v_res_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2650_, v_as_2651_, v_sz_boxed_2655_, v_i_boxed_2656_, v_b_2654_);
lean_dec_ref(v_as_2651_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2663_, lean_object* v_sep_2664_){
_start:
{
lean_object* v___x_2665_; size_t v_sz_2666_; size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v_snd_2669_; 
v___x_2665_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2666_ = lean_array_size(v_as_2663_);
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2664_, v_as_2663_, v_sz_2666_, v___x_2667_, v___x_2665_);
v_snd_2669_ = lean_ctor_get(v___x_2668_, 1);
lean_inc(v_snd_2669_);
lean_dec_ref(v___x_2668_);
return v_snd_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2670_, lean_object* v_sep_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_mkSepArray(v_as_2670_, v_sep_2671_);
lean_dec_ref(v_as_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2680_){
_start:
{
if (lean_obj_tag(v_arg_2680_) == 0)
{
lean_object* v___x_2681_; 
v___x_2681_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2681_;
}
else
{
lean_object* v_val_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_val_2682_ = lean_ctor_get(v_arg_2680_, 0);
lean_inc(v_val_2682_);
lean_dec_ref_known(v_arg_2680_, 1);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_mk_empty_array_with_capacity(v___x_2683_);
v___x_2685_ = lean_array_push(v___x_2684_, v_val_2682_);
v___x_2686_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2687_ = lean_box(2);
v___x_2688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v___x_2686_);
lean_ctor_set(v___x_2688_, 2, v___x_2685_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2695_, uint8_t v_canonical_2696_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2697_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2698_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2699_ = l_Lean_mkAtomFrom(v_ref_2695_, v___x_2698_, v_canonical_2696_);
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_mk_empty_array_with_capacity(v___x_2700_);
v___x_2702_ = lean_array_push(v___x_2701_, v___x_2699_);
v___x_2703_ = lean_box(2);
v___x_2704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2697_);
lean_ctor_set(v___x_2704_, 2, v___x_2702_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2705_, lean_object* v_canonical_2706_){
_start:
{
uint8_t v_canonical_boxed_2707_; lean_object* v_res_2708_; 
v_canonical_boxed_2707_ = lean_unbox(v_canonical_2706_);
v_res_2708_ = l_Lean_mkHole(v_ref_2705_, v_canonical_boxed_2707_);
lean_dec(v_ref_2705_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2709_, lean_object* v_sep_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2711_ = l_Lean_mkSepArray(v_a_2709_, v_sep_2710_);
v___x_2712_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2713_ = lean_box(2);
v___x_2714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
lean_ctor_set(v___x_2714_, 2, v___x_2711_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2715_, lean_object* v_sep_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Syntax_mkSep(v_a_2715_, v_sep_2716_);
lean_dec_ref(v_a_2715_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2724_, lean_object* v_elems_2725_){
_start:
{
uint8_t v___x_2726_; 
lean_inc_ref(v_sep_2724_);
v___x_2726_ = lean_string_isempty(v_sep_2724_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = l_Lean_mkAtom(v_sep_2724_);
v___x_2728_ = l_Lean_mkSepArray(v_elems_2725_, v___x_2727_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref(v_sep_2724_);
v___x_2729_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2730_ = l_Lean_mkSepArray(v_elems_2725_, v___x_2729_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2731_, lean_object* v_elems_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2731_, v_elems_2732_);
lean_dec_ref(v_elems_2732_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2734_, lean_object* v_toPure_2735_, lean_object* v_sep_2736_, lean_object* v_ref_2737_){
_start:
{
lean_object* v___y_2739_; uint8_t v___x_2742_; 
lean_inc_ref(v_sep_2736_);
v___x_2742_ = lean_string_isempty(v_sep_2736_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_mkAtomFrom(v_ref_2737_, v_sep_2736_, v___x_2742_);
v___y_2739_ = v___x_2743_;
goto v___jp_2738_;
}
else
{
lean_object* v___x_2744_; 
lean_dec_ref(v_sep_2736_);
v___x_2744_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2739_ = v___x_2744_;
goto v___jp_2738_;
}
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = l_Lean_mkSepArray(v_elems_2734_, v___y_2739_);
v___x_2741_ = lean_apply_2(v_toPure_2735_, lean_box(0), v___x_2740_);
return v___x_2741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2745_, lean_object* v_toPure_2746_, lean_object* v_sep_2747_, lean_object* v_ref_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2745_, v_toPure_2746_, v_sep_2747_, v_ref_2748_);
lean_dec(v_ref_2748_);
lean_dec_ref(v_elems_2745_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_sep_2752_, lean_object* v_elems_2753_){
_start:
{
lean_object* v_toApplicative_2754_; lean_object* v_toBind_2755_; lean_object* v_getRef_2756_; lean_object* v_toPure_2757_; lean_object* v___f_2758_; lean_object* v___x_2759_; 
v_toApplicative_2754_ = lean_ctor_get(v_inst_2750_, 0);
lean_inc_ref(v_toApplicative_2754_);
v_toBind_2755_ = lean_ctor_get(v_inst_2750_, 1);
lean_inc(v_toBind_2755_);
lean_dec_ref(v_inst_2750_);
v_getRef_2756_ = lean_ctor_get(v_inst_2751_, 0);
lean_inc(v_getRef_2756_);
lean_dec_ref(v_inst_2751_);
v_toPure_2757_ = lean_ctor_get(v_toApplicative_2754_, 1);
lean_inc(v_toPure_2757_);
lean_dec_ref(v_toApplicative_2754_);
v___f_2758_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2758_, 0, v_elems_2753_);
lean_closure_set(v___f_2758_, 1, v_toPure_2757_);
lean_closure_set(v___f_2758_, 2, v_sep_2752_);
v___x_2759_ = lean_apply_4(v_toBind_2755_, lean_box(0), lean_box(0), v_getRef_2756_, v___f_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2760_, lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_sep_2763_, lean_object* v_elems_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2761_, v_inst_2762_, v_sep_2763_, v_elems_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2766_, lean_object* v_elems_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2766_, v_elems_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2769_, lean_object* v_elems_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2769_, v_elems_2770_);
lean_dec_ref(v_elems_2770_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2772_, lean_object* v_sep_2773_, lean_object* v_elems_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2773_, v_elems_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2776_, lean_object* v_sep_2777_, lean_object* v_elems_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2776_, v_sep_2777_, v_elems_2778_);
lean_dec_ref(v_elems_2778_);
lean_dec(v_k_2776_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2780_, lean_object* v_sep_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2782_, 0, v_k_2780_);
lean_closure_set(v___x_2782_, 1, v_sep_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2789_, lean_object* v_x_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2791_ = lean_array_get_size(v_x_2790_);
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = lean_nat_dec_eq(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2794_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2795_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2796_ = lean_box(2);
v___x_2797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v___x_2795_);
lean_ctor_set(v___x_2797_, 2, v_x_2790_);
v___x_2798_ = lean_unsigned_to_nat(2u);
v___x_2799_ = lean_mk_empty_array_with_capacity(v___x_2798_);
v___x_2800_ = lean_array_push(v___x_2799_, v_fn_2789_);
v___x_2801_ = lean_array_push(v___x_2800_, v___x_2797_);
v___x_2802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2796_);
lean_ctor_set(v___x_2802_, 1, v___x_2794_);
lean_ctor_set(v___x_2802_, 2, v___x_2801_);
return v___x_2802_;
}
else
{
lean_dec_ref(v_x_2790_);
return v_fn_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2803_, lean_object* v_args_2804_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = l_Lean_mkCIdent(v_fn_2803_);
v___x_2806_ = l_Lean_Syntax_mkApp(v___x_2805_, v_args_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2807_, lean_object* v_val_2808_, lean_object* v_info_2809_){
_start:
{
lean_object* v_atom_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_atom_2810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2810_, 0, v_info_2809_);
lean_ctor_set(v_atom_2810_, 1, v_val_2808_);
v___x_2811_ = lean_unsigned_to_nat(1u);
v___x_2812_ = lean_mk_empty_array_with_capacity(v___x_2811_);
v___x_2813_ = lean_array_push(v___x_2812_, v_atom_2810_);
v___x_2814_ = lean_box(2);
v___x_2815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_kind_2807_);
lean_ctor_set(v___x_2815_, 2, v___x_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2819_, lean_object* v_info_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2822_ = l_Char_quote(v_val_2819_);
v___x_2823_ = l_Lean_Syntax_mkLit(v___x_2821_, v___x_2822_, v_info_2820_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2824_, lean_object* v_info_2825_){
_start:
{
uint32_t v_val_boxed_2826_; lean_object* v_res_2827_; 
v_val_boxed_2826_ = lean_unbox_uint32(v_val_2824_);
lean_dec(v_val_2824_);
v_res_2827_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2826_, v_info_2825_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2831_, lean_object* v_info_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2834_ = l_String_quote(v_val_2831_);
v___x_2835_ = l_Lean_Syntax_mkLit(v___x_2833_, v___x_2834_, v_info_2832_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2839_, lean_object* v_info_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2842_ = l_Lean_Syntax_mkLit(v___x_2841_, v_val_2839_, v_info_2840_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2843_, lean_object* v_info_2844_){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2846_ = l_Nat_reprFast(v_val_2843_);
v___x_2847_ = l_Lean_Syntax_mkLit(v___x_2845_, v___x_2846_, v_info_2844_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2851_, lean_object* v_info_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2854_ = l_Lean_Syntax_mkLit(v___x_2853_, v_val_2851_, v_info_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2858_, lean_object* v_info_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2861_ = l_Lean_Syntax_mkLit(v___x_2860_, v_val_2858_, v_info_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2862_, lean_object* v_i_2863_, lean_object* v_val_2864_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_string_utf8_at_end(v_s_2862_, v_i_2863_);
if (v___x_2865_ == 0)
{
uint32_t v_c_2866_; uint32_t v___x_2867_; uint8_t v___x_2868_; 
v_c_2866_ = lean_string_utf8_get(v_s_2862_, v_i_2863_);
v___x_2867_ = 48;
v___x_2868_ = lean_uint32_dec_eq(v_c_2866_, v___x_2867_);
if (v___x_2868_ == 0)
{
uint32_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = 49;
v___x_2870_ = lean_uint32_dec_eq(v_c_2866_, v___x_2869_);
if (v___x_2870_ == 0)
{
uint32_t v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = 95;
v___x_2872_ = lean_uint32_dec_eq(v_c_2866_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_dec(v_val_2864_);
lean_dec(v_i_2863_);
v___x_2873_ = lean_box(0);
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_string_utf8_next(v_s_2862_, v_i_2863_);
lean_dec(v_i_2863_);
v_i_2863_ = v___x_2874_;
goto _start;
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2876_ = lean_string_utf8_next(v_s_2862_, v_i_2863_);
lean_dec(v_i_2863_);
v___x_2877_ = lean_unsigned_to_nat(2u);
v___x_2878_ = lean_nat_mul(v___x_2877_, v_val_2864_);
lean_dec(v_val_2864_);
v___x_2879_ = lean_unsigned_to_nat(1u);
v___x_2880_ = lean_nat_add(v___x_2878_, v___x_2879_);
lean_dec(v___x_2878_);
v_i_2863_ = v___x_2876_;
v_val_2864_ = v___x_2880_;
goto _start;
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_string_utf8_next(v_s_2862_, v_i_2863_);
lean_dec(v_i_2863_);
v___x_2883_ = lean_unsigned_to_nat(2u);
v___x_2884_ = lean_nat_mul(v___x_2883_, v_val_2864_);
lean_dec(v_val_2864_);
v_i_2863_ = v___x_2882_;
v_val_2864_ = v___x_2884_;
goto _start;
}
}
else
{
lean_object* v___x_2886_; 
lean_dec(v_i_2863_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_val_2864_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2887_, lean_object* v_i_2888_, lean_object* v_val_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2887_, v_i_2888_, v_val_2889_);
lean_dec_ref(v_s_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2891_, lean_object* v_i_2892_, lean_object* v_val_2893_){
_start:
{
uint8_t v___x_2894_; 
v___x_2894_ = lean_string_utf8_at_end(v_s_2891_, v_i_2892_);
if (v___x_2894_ == 0)
{
uint32_t v_c_2895_; uint32_t v___x_2902_; uint8_t v___x_2903_; 
v_c_2895_ = lean_string_utf8_get(v_s_2891_, v_i_2892_);
v___x_2902_ = 48;
v___x_2903_ = lean_uint32_dec_le(v___x_2902_, v_c_2895_);
if (v___x_2903_ == 0)
{
goto v___jp_2896_;
}
else
{
uint32_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = 55;
v___x_2905_ = lean_uint32_dec_le(v_c_2895_, v___x_2904_);
if (v___x_2905_ == 0)
{
goto v___jp_2896_;
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2906_ = lean_string_utf8_next(v_s_2891_, v_i_2892_);
lean_dec(v_i_2892_);
v___x_2907_ = lean_unsigned_to_nat(8u);
v___x_2908_ = lean_nat_mul(v___x_2907_, v_val_2893_);
lean_dec(v_val_2893_);
v___x_2909_ = lean_uint32_to_nat(v_c_2895_);
v___x_2910_ = lean_nat_add(v___x_2908_, v___x_2909_);
lean_dec(v___x_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_unsigned_to_nat(48u);
v___x_2912_ = lean_nat_sub(v___x_2910_, v___x_2911_);
lean_dec(v___x_2910_);
v_i_2892_ = v___x_2906_;
v_val_2893_ = v___x_2912_;
goto _start;
}
}
v___jp_2896_:
{
uint32_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = 95;
v___x_2898_ = lean_uint32_dec_eq(v_c_2895_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_val_2893_);
lean_dec(v_i_2892_);
v___x_2899_ = lean_box(0);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_string_utf8_next(v_s_2891_, v_i_2892_);
lean_dec(v_i_2892_);
v_i_2892_ = v___x_2900_;
goto _start;
}
}
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_i_2892_);
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_val_2893_);
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
uint32_t v_c_2988_; uint32_t v___x_2995_; uint8_t v___x_2996_; 
v_c_2988_ = lean_string_utf8_get(v_s_2984_, v_i_2985_);
v___x_2995_ = 48;
v___x_2996_ = lean_uint32_dec_le(v___x_2995_, v_c_2988_);
if (v___x_2996_ == 0)
{
goto v___jp_2989_;
}
else
{
uint32_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = 57;
v___x_2998_ = lean_uint32_dec_le(v_c_2988_, v___x_2997_);
if (v___x_2998_ == 0)
{
goto v___jp_2989_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_2999_ = lean_string_utf8_next(v_s_2984_, v_i_2985_);
lean_dec(v_i_2985_);
v___x_3000_ = lean_unsigned_to_nat(10u);
v___x_3001_ = lean_nat_mul(v___x_3000_, v_val_2986_);
lean_dec(v_val_2986_);
v___x_3002_ = lean_uint32_to_nat(v_c_2988_);
v___x_3003_ = lean_nat_add(v___x_3001_, v___x_3002_);
lean_dec(v___x_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_unsigned_to_nat(48u);
v___x_3005_ = lean_nat_sub(v___x_3003_, v___x_3004_);
lean_dec(v___x_3003_);
v_i_2985_ = v___x_2999_;
v_val_2986_ = v___x_3005_;
goto _start;
}
}
v___jp_2989_:
{
uint32_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = 95;
v___x_2991_ = lean_uint32_dec_eq(v_c_2988_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_dec(v_val_2986_);
lean_dec(v_i_2985_);
v___x_2992_ = lean_box(0);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_string_utf8_next(v_s_2984_, v_i_2985_);
lean_dec(v_i_2985_);
v_i_2985_ = v___x_2993_;
goto _start;
}
}
}
else
{
lean_object* v___x_3007_; 
lean_dec(v_i_2985_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_val_2986_);
return v___x_3007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3008_, lean_object* v_i_3009_, lean_object* v_val_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3008_, v_i_3009_, v_val_3010_);
lean_dec_ref(v_s_3008_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3014_){
_start:
{
lean_object* v_len_3015_; lean_object* v___x_3016_; uint8_t v___x_3026_; 
v_len_3015_ = lean_string_length(v_s_3014_);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3026_ = lean_nat_dec_eq(v_len_3015_, v___x_3016_);
if (v___x_3026_ == 0)
{
uint32_t v_c_3027_; uint32_t v___x_3028_; uint8_t v___x_3029_; 
v_c_3027_ = lean_string_utf8_get(v_s_3014_, v___x_3016_);
v___x_3028_ = 48;
v___x_3029_ = lean_uint32_dec_eq(v_c_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
uint8_t v___x_3030_; 
lean_dec(v_len_3015_);
v___x_3030_ = lean_uint32_dec_le(v___x_3028_, v_c_3027_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_box(0);
return v___x_3031_;
}
else
{
uint32_t v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = 57;
v___x_3033_ = lean_uint32_dec_le(v_c_3027_, v___x_3032_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_box(0);
return v___x_3034_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3014_, v___x_3016_, v___x_3016_);
return v___x_3035_;
}
}
}
else
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_dec_eq(v_len_3015_, v___x_3036_);
lean_dec(v_len_3015_);
if (v___x_3037_ == 0)
{
uint32_t v_c_3038_; uint32_t v___x_3039_; uint8_t v___x_3040_; 
v_c_3038_ = lean_string_utf8_get(v_s_3014_, v___x_3036_);
v___x_3039_ = 120;
v___x_3040_ = lean_uint32_dec_eq(v_c_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
uint32_t v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = 88;
v___x_3042_ = lean_uint32_dec_eq(v_c_3038_, v___x_3041_);
if (v___x_3042_ == 0)
{
uint32_t v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = 98;
v___x_3044_ = lean_uint32_dec_eq(v_c_3038_, v___x_3043_);
if (v___x_3044_ == 0)
{
uint32_t v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = 66;
v___x_3046_ = lean_uint32_dec_eq(v_c_3038_, v___x_3045_);
if (v___x_3046_ == 0)
{
uint32_t v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = 111;
v___x_3048_ = lean_uint32_dec_eq(v_c_3038_, v___x_3047_);
if (v___x_3048_ == 0)
{
uint32_t v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = 79;
v___x_3050_ = lean_uint32_dec_eq(v_c_3038_, v___x_3049_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_uint32_dec_le(v___x_3028_, v_c_3038_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_box(0);
return v___x_3052_;
}
else
{
uint32_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = 57;
v___x_3054_ = lean_uint32_dec_le(v_c_3038_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_box(0);
return v___x_3055_;
}
else
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3014_, v___x_3016_, v___x_3016_);
return v___x_3056_;
}
}
}
else
{
goto v___jp_3017_;
}
}
else
{
goto v___jp_3017_;
}
}
else
{
goto v___jp_3020_;
}
}
else
{
goto v___jp_3020_;
}
}
else
{
goto v___jp_3023_;
}
}
else
{
goto v___jp_3023_;
}
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3057_;
}
}
}
else
{
lean_object* v___x_3058_; 
lean_dec(v_len_3015_);
v___x_3058_ = lean_box(0);
return v___x_3058_;
}
v___jp_3017_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(2u);
v___x_3019_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3014_, v___x_3018_, v___x_3016_);
return v___x_3019_;
}
v___jp_3020_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_unsigned_to_nat(2u);
v___x_3022_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3014_, v___x_3021_, v___x_3016_);
return v___x_3022_;
}
v___jp_3023_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_unsigned_to_nat(2u);
v___x_3025_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3014_, v___x_3024_, v___x_3016_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3059_);
lean_dec_ref(v_s_3059_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3061_, lean_object* v_stx_3062_){
_start:
{
if (lean_obj_tag(v_stx_3062_) == 1)
{
lean_object* v_kind_3063_; lean_object* v_args_3064_; uint8_t v___x_3065_; 
v_kind_3063_ = lean_ctor_get(v_stx_3062_, 1);
v_args_3064_ = lean_ctor_get(v_stx_3062_, 2);
v___x_3065_ = lean_name_eq(v_kind_3063_, v_litKind_3061_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_box(0);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3067_ = lean_array_get_size(v_args_3064_);
v___x_3068_ = lean_unsigned_to_nat(1u);
v___x_3069_ = lean_nat_dec_eq(v___x_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_box(0);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = lean_array_fget_borrowed(v_args_3064_, v___x_3071_);
if (lean_obj_tag(v___x_3072_) == 2)
{
lean_object* v_val_3073_; lean_object* v___x_3074_; 
v_val_3073_ = lean_ctor_get(v___x_3072_, 1);
lean_inc_ref(v_val_3073_);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_val_3073_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_box(0);
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_box(0);
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3077_, lean_object* v_stx_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_Syntax_isLit_x3f(v_litKind_3077_, v_stx_3078_);
lean_dec(v_stx_3078_);
lean_dec(v_litKind_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3080_, lean_object* v_stx_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Syntax_isLit_x3f(v_litKind_3080_, v_stx_3081_);
if (lean_obj_tag(v___x_3082_) == 1)
{
lean_object* v_val_3083_; lean_object* v___x_3084_; 
v_val_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_val_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3084_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3083_);
lean_dec(v_val_3083_);
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; 
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3086_, lean_object* v_stx_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3086_, v_stx_3087_);
lean_dec(v_stx_3087_);
lean_dec(v_litKind_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3089_){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3091_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3090_, v_s_3089_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Syntax_isNatLit_x3f(v_s_3092_);
lean_dec(v_s_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3097_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3099_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3098_, v_s_3097_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3100_);
lean_dec(v_s_3100_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3102_, lean_object* v_i_3103_, lean_object* v_val_3104_, lean_object* v_e_3105_, uint8_t v_sign_3106_, lean_object* v_exp_3107_){
_start:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_string_utf8_at_end(v_s_3102_, v_i_3103_);
if (v___x_3108_ == 0)
{
uint32_t v_c_3109_; uint32_t v___x_3116_; uint8_t v___x_3117_; 
v_c_3109_ = lean_string_utf8_get(v_s_3102_, v_i_3103_);
v___x_3116_ = 48;
v___x_3117_ = lean_uint32_dec_le(v___x_3116_, v_c_3109_);
if (v___x_3117_ == 0)
{
goto v___jp_3110_;
}
else
{
uint32_t v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = 57;
v___x_3119_ = lean_uint32_dec_le(v_c_3109_, v___x_3118_);
if (v___x_3119_ == 0)
{
goto v___jp_3110_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3120_ = lean_string_utf8_next(v_s_3102_, v_i_3103_);
lean_dec(v_i_3103_);
v___x_3121_ = lean_unsigned_to_nat(10u);
v___x_3122_ = lean_nat_mul(v___x_3121_, v_exp_3107_);
lean_dec(v_exp_3107_);
v___x_3123_ = lean_uint32_to_nat(v_c_3109_);
v___x_3124_ = lean_nat_add(v___x_3122_, v___x_3123_);
lean_dec(v___x_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_unsigned_to_nat(48u);
v___x_3126_ = lean_nat_sub(v___x_3124_, v___x_3125_);
lean_dec(v___x_3124_);
v_i_3103_ = v___x_3120_;
v_exp_3107_ = v___x_3126_;
goto _start;
}
}
v___jp_3110_:
{
uint32_t v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = 95;
v___x_3112_ = lean_uint32_dec_eq(v_c_3109_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec(v_exp_3107_);
lean_dec(v_val_3104_);
lean_dec(v_i_3103_);
v___x_3113_ = lean_box(0);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_string_utf8_next(v_s_3102_, v_i_3103_);
lean_dec(v_i_3103_);
v_i_3103_ = v___x_3114_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3103_);
if (v_sign_3106_ == 0)
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_nat_dec_le(v_e_3105_, v_exp_3107_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3129_ = lean_nat_sub(v_e_3105_, v_exp_3107_);
lean_dec(v_exp_3107_);
v___x_3130_ = lean_box(v___x_3108_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3129_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_val_3104_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3134_ = lean_nat_sub(v_exp_3107_, v_e_3105_);
lean_dec(v_exp_3107_);
v___x_3135_ = lean_box(v_sign_3106_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
lean_ctor_set(v___x_3136_, 1, v___x_3134_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v_val_3104_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3139_ = lean_nat_add(v_exp_3107_, v_e_3105_);
lean_dec(v_exp_3107_);
v___x_3140_ = lean_box(v_sign_3106_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3139_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_val_3104_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3144_, lean_object* v_i_3145_, lean_object* v_val_3146_, lean_object* v_e_3147_, lean_object* v_sign_3148_, lean_object* v_exp_3149_){
_start:
{
uint8_t v_sign_boxed_3150_; lean_object* v_res_3151_; 
v_sign_boxed_3150_ = lean_unbox(v_sign_3148_);
v_res_3151_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3144_, v_i_3145_, v_val_3146_, v_e_3147_, v_sign_boxed_3150_, v_exp_3149_);
lean_dec(v_e_3147_);
lean_dec_ref(v_s_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3152_, lean_object* v_i_3153_, lean_object* v_val_3154_, lean_object* v_e_3155_){
_start:
{
uint8_t v___x_3156_; 
v___x_3156_ = lean_string_utf8_at_end(v_s_3152_, v_i_3153_);
if (v___x_3156_ == 0)
{
uint32_t v_c_3157_; uint32_t v___x_3158_; uint8_t v___x_3159_; 
v_c_3157_ = lean_string_utf8_get(v_s_3152_, v_i_3153_);
v___x_3158_ = 45;
v___x_3159_ = lean_uint32_dec_eq(v_c_3157_, v___x_3158_);
if (v___x_3159_ == 0)
{
uint32_t v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = 43;
v___x_3161_ = lean_uint32_dec_eq(v_c_3157_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3152_, v_i_3153_, v_val_3154_, v_e_3155_, v___x_3161_, v___x_3162_);
return v___x_3163_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_string_utf8_next(v_s_3152_, v_i_3153_);
lean_dec(v_i_3153_);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3152_, v___x_3164_, v_val_3154_, v_e_3155_, v___x_3159_, v___x_3165_);
return v___x_3166_;
}
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_string_utf8_next(v_s_3152_, v_i_3153_);
lean_dec(v_i_3153_);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3152_, v___x_3167_, v_val_3154_, v_e_3155_, v___x_3159_, v___x_3168_);
return v___x_3169_;
}
}
else
{
lean_object* v___x_3170_; 
lean_dec(v_val_3154_);
lean_dec(v_i_3153_);
v___x_3170_ = lean_box(0);
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3171_, lean_object* v_i_3172_, lean_object* v_val_3173_, lean_object* v_e_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3171_, v_i_3172_, v_val_3173_, v_e_3174_);
lean_dec(v_e_3174_);
lean_dec_ref(v_s_3171_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3176_, lean_object* v_i_3177_, lean_object* v_val_3178_, lean_object* v_e_3179_){
_start:
{
uint8_t v___x_3183_; 
v___x_3183_ = lean_string_utf8_at_end(v_s_3176_, v_i_3177_);
if (v___x_3183_ == 0)
{
uint32_t v_c_3184_; uint32_t v___x_3195_; uint8_t v___x_3196_; 
v_c_3184_ = lean_string_utf8_get(v_s_3176_, v_i_3177_);
v___x_3195_ = 48;
v___x_3196_ = lean_uint32_dec_le(v___x_3195_, v_c_3184_);
if (v___x_3196_ == 0)
{
goto v___jp_3185_;
}
else
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 57;
v___x_3198_ = lean_uint32_dec_le(v_c_3184_, v___x_3197_);
if (v___x_3198_ == 0)
{
goto v___jp_3185_;
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3199_ = lean_string_utf8_next(v_s_3176_, v_i_3177_);
lean_dec(v_i_3177_);
v___x_3200_ = lean_unsigned_to_nat(10u);
v___x_3201_ = lean_nat_mul(v___x_3200_, v_val_3178_);
lean_dec(v_val_3178_);
v___x_3202_ = lean_uint32_to_nat(v_c_3184_);
v___x_3203_ = lean_nat_add(v___x_3201_, v___x_3202_);
lean_dec(v___x_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_unsigned_to_nat(48u);
v___x_3205_ = lean_nat_sub(v___x_3203_, v___x_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_unsigned_to_nat(1u);
v___x_3207_ = lean_nat_add(v_e_3179_, v___x_3206_);
lean_dec(v_e_3179_);
v_i_3177_ = v___x_3199_;
v_val_3178_ = v___x_3205_;
v_e_3179_ = v___x_3207_;
goto _start;
}
}
v___jp_3185_:
{
uint32_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = 95;
v___x_3187_ = lean_uint32_dec_eq(v_c_3184_, v___x_3186_);
if (v___x_3187_ == 0)
{
uint32_t v___x_3188_; uint8_t v___x_3189_; 
v___x_3188_ = 101;
v___x_3189_ = lean_uint32_dec_eq(v_c_3184_, v___x_3188_);
if (v___x_3189_ == 0)
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 69;
v___x_3191_ = lean_uint32_dec_eq(v_c_3184_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; 
lean_dec(v_e_3179_);
lean_dec(v_val_3178_);
lean_dec(v_i_3177_);
v___x_3192_ = lean_box(0);
return v___x_3192_;
}
else
{
goto v___jp_3180_;
}
}
else
{
goto v___jp_3180_;
}
}
else
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_string_utf8_next(v_s_3176_, v_i_3177_);
lean_dec(v_i_3177_);
v_i_3177_ = v___x_3193_;
goto _start;
}
}
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec(v_i_3177_);
v___x_3209_ = lean_box(v___x_3183_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v_e_3179_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_val_3178_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
v___jp_3180_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_string_utf8_next(v_s_3176_, v_i_3177_);
lean_dec(v_i_3177_);
v___x_3182_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3176_, v___x_3181_, v_val_3178_, v_e_3179_);
lean_dec(v_e_3179_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3213_, lean_object* v_i_3214_, lean_object* v_val_3215_, lean_object* v_e_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3213_, v_i_3214_, v_val_3215_, v_e_3216_);
lean_dec_ref(v_s_3213_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3218_, lean_object* v_i_3219_, lean_object* v_val_3220_){
_start:
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_string_utf8_at_end(v_s_3218_, v_i_3219_);
if (v___x_3225_ == 0)
{
uint32_t v_c_3226_; uint32_t v___x_3242_; uint8_t v___x_3243_; 
v_c_3226_ = lean_string_utf8_get(v_s_3218_, v_i_3219_);
v___x_3242_ = 48;
v___x_3243_ = lean_uint32_dec_le(v___x_3242_, v_c_3226_);
if (v___x_3243_ == 0)
{
goto v___jp_3227_;
}
else
{
uint32_t v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = 57;
v___x_3245_ = lean_uint32_dec_le(v_c_3226_, v___x_3244_);
if (v___x_3245_ == 0)
{
goto v___jp_3227_;
}
else
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3246_ = lean_string_utf8_next(v_s_3218_, v_i_3219_);
lean_dec(v_i_3219_);
v___x_3247_ = lean_unsigned_to_nat(10u);
v___x_3248_ = lean_nat_mul(v___x_3247_, v_val_3220_);
lean_dec(v_val_3220_);
v___x_3249_ = lean_uint32_to_nat(v_c_3226_);
v___x_3250_ = lean_nat_add(v___x_3248_, v___x_3249_);
lean_dec(v___x_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_unsigned_to_nat(48u);
v___x_3252_ = lean_nat_sub(v___x_3250_, v___x_3251_);
lean_dec(v___x_3250_);
v_i_3219_ = v___x_3246_;
v_val_3220_ = v___x_3252_;
goto _start;
}
}
v___jp_3227_:
{
uint32_t v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = 95;
v___x_3229_ = lean_uint32_dec_eq(v_c_3226_, v___x_3228_);
if (v___x_3229_ == 0)
{
uint32_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = 46;
v___x_3231_ = lean_uint32_dec_eq(v_c_3226_, v___x_3230_);
if (v___x_3231_ == 0)
{
uint32_t v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = 101;
v___x_3233_ = lean_uint32_dec_eq(v_c_3226_, v___x_3232_);
if (v___x_3233_ == 0)
{
uint32_t v___x_3234_; uint8_t v___x_3235_; 
v___x_3234_ = 69;
v___x_3235_ = lean_uint32_dec_eq(v_c_3226_, v___x_3234_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; 
lean_dec(v_val_3220_);
lean_dec(v_i_3219_);
v___x_3236_ = lean_box(0);
return v___x_3236_;
}
else
{
goto v___jp_3221_;
}
}
else
{
goto v___jp_3221_;
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_string_utf8_next(v_s_3218_, v_i_3219_);
lean_dec(v_i_3219_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3218_, v___x_3237_, v_val_3220_, v___x_3238_);
return v___x_3239_;
}
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_string_utf8_next(v_s_3218_, v_i_3219_);
lean_dec(v_i_3219_);
v_i_3219_ = v___x_3240_;
goto _start;
}
}
}
else
{
lean_object* v___x_3254_; 
lean_dec(v_val_3220_);
lean_dec(v_i_3219_);
v___x_3254_ = lean_box(0);
return v___x_3254_;
}
v___jp_3221_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = lean_string_utf8_next(v_s_3218_, v_i_3219_);
lean_dec(v_i_3219_);
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3218_, v___x_3222_, v_val_3220_, v___x_3223_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3255_, lean_object* v_i_3256_, lean_object* v_val_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3255_, v_i_3256_, v_val_3257_);
lean_dec_ref(v_s_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3259_){
_start:
{
lean_object* v_len_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v_len_3260_ = lean_string_length(v_s_3259_);
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = lean_nat_dec_eq(v_len_3260_, v___x_3261_);
lean_dec(v_len_3260_);
if (v___x_3262_ == 0)
{
uint32_t v_c_3263_; uint32_t v___x_3264_; uint8_t v___x_3265_; 
v_c_3263_ = lean_string_utf8_get(v_s_3259_, v___x_3261_);
v___x_3264_ = 48;
v___x_3265_ = lean_uint32_dec_le(v___x_3264_, v_c_3263_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_box(0);
return v___x_3266_;
}
else
{
uint32_t v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = 57;
v___x_3268_ = lean_uint32_dec_le(v_c_3263_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_box(0);
return v___x_3269_;
}
else
{
lean_object* v___x_3270_; 
v___x_3270_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3259_, v___x_3261_, v___x_3261_);
return v___x_3270_;
}
}
}
else
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_box(0);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3272_);
lean_dec_ref(v_s_3272_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3274_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3276_ = l_Lean_Syntax_isLit_x3f(v___x_3275_, v_stx_3274_);
if (lean_obj_tag(v___x_3276_) == 1)
{
lean_object* v_val_3277_; lean_object* v___x_3278_; 
v_val_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3277_);
lean_dec(v_val_3277_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; 
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
return v___x_3279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3280_);
lean_dec(v_stx_3280_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3282_){
_start:
{
switch(lean_obj_tag(v_x_3282_))
{
case 2:
{
lean_object* v_val_3283_; lean_object* v___x_3284_; 
v_val_3283_ = lean_ctor_get(v_x_3282_, 1);
lean_inc_ref(v_val_3283_);
lean_dec_ref_known(v_x_3282_, 2);
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_val_3283_);
return v___x_3284_;
}
case 3:
{
lean_object* v_rawVal_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_rawVal_3285_ = lean_ctor_get(v_x_3282_, 1);
lean_inc_ref(v_rawVal_3285_);
lean_dec_ref_known(v_x_3282_, 4);
v___x_3286_ = lean_substring_tostring(v_rawVal_3285_);
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
default: 
{
lean_object* v___x_3288_; 
lean_dec(v_x_3282_);
v___x_3288_ = lean_box(0);
return v___x_3288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3289_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_unsigned_to_nat(0u);
return v___x_3291_;
}
else
{
lean_object* v_val_3292_; 
v_val_3292_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_val_3292_);
lean_dec_ref_known(v___x_3290_, 1);
return v_val_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_Syntax_toNat(v_stx_3293_);
lean_dec(v_stx_3293_);
return v_res_3294_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = 9;
v___x_3296_ = lean_box_uint32(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = 10;
v___x_3298_ = lean_box_uint32(v___x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = 13;
v___x_3300_ = lean_box_uint32(v___x_3299_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = 39;
v___x_3302_ = lean_box_uint32(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = 34;
v___x_3304_ = lean_box_uint32(v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = 92;
v___x_3306_ = lean_box_uint32(v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3307_, lean_object* v_i_3308_){
_start:
{
uint32_t v_c_3309_; lean_object* v_i_3310_; uint32_t v___x_3311_; uint8_t v___x_3312_; 
v_c_3309_ = lean_string_utf8_get(v_s_3307_, v_i_3308_);
v_i_3310_ = lean_string_utf8_next(v_s_3307_, v_i_3308_);
v___x_3311_ = 92;
v___x_3312_ = lean_uint32_dec_eq(v_c_3309_, v___x_3311_);
if (v___x_3312_ == 0)
{
uint32_t v___x_3313_; uint8_t v___x_3314_; 
v___x_3313_ = 34;
v___x_3314_ = lean_uint32_dec_eq(v_c_3309_, v___x_3313_);
if (v___x_3314_ == 0)
{
uint32_t v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = 39;
v___x_3316_ = lean_uint32_dec_eq(v_c_3309_, v___x_3315_);
if (v___x_3316_ == 0)
{
uint32_t v___x_3317_; uint8_t v___x_3318_; 
v___x_3317_ = 114;
v___x_3318_ = lean_uint32_dec_eq(v_c_3309_, v___x_3317_);
if (v___x_3318_ == 0)
{
uint32_t v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = 110;
v___x_3320_ = lean_uint32_dec_eq(v_c_3309_, v___x_3319_);
if (v___x_3320_ == 0)
{
uint32_t v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = 116;
v___x_3322_ = lean_uint32_dec_eq(v_c_3309_, v___x_3321_);
if (v___x_3322_ == 0)
{
uint32_t v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = 120;
v___x_3324_ = lean_uint32_dec_eq(v_c_3309_, v___x_3323_);
if (v___x_3324_ == 0)
{
uint32_t v___x_3325_; uint8_t v___x_3326_; 
v___x_3325_ = 117;
v___x_3326_ = lean_uint32_dec_eq(v_c_3309_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
lean_dec(v_i_3310_);
v___x_3327_ = lean_box(0);
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3307_, v_i_3310_);
lean_dec(v_i_3310_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
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
v___x_3333_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3307_, v_snd_3332_);
lean_dec(v_snd_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; 
lean_dec(v_fst_3331_);
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
v___x_3338_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3307_, v_snd_3337_);
lean_dec(v_snd_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; 
lean_dec(v_fst_3336_);
lean_dec(v_fst_3331_);
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
v___x_3343_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3307_, v_snd_3342_);
lean_dec(v_snd_3342_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec(v_fst_3341_);
lean_dec(v_fst_3336_);
lean_dec(v_fst_3331_);
v___x_3344_ = lean_box(0);
return v___x_3344_;
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3370_; 
v_val_3345_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3347_ = v___x_3343_;
v_isShared_3348_ = v_isSharedCheck_3370_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_val_3345_);
lean_dec(v___x_3343_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3370_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3369_; 
v_fst_3349_ = lean_ctor_get(v_val_3345_, 0);
v_snd_3350_ = lean_ctor_get(v_val_3345_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_val_3345_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3352_ = v_val_3345_;
v_isShared_3353_ = v_isSharedCheck_3369_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snd_3350_);
lean_inc(v_fst_3349_);
lean_dec(v_val_3345_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3369_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint32_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3354_ = lean_unsigned_to_nat(16u);
v___x_3355_ = lean_nat_mul(v___x_3354_, v_fst_3331_);
lean_dec(v_fst_3331_);
v___x_3356_ = lean_nat_add(v___x_3355_, v_fst_3336_);
lean_dec(v_fst_3336_);
lean_dec(v___x_3355_);
v___x_3357_ = lean_nat_mul(v___x_3354_, v___x_3356_);
lean_dec(v___x_3356_);
v___x_3358_ = lean_nat_add(v___x_3357_, v_fst_3341_);
lean_dec(v_fst_3341_);
lean_dec(v___x_3357_);
v___x_3359_ = lean_nat_mul(v___x_3354_, v___x_3358_);
lean_dec(v___x_3358_);
v___x_3360_ = lean_nat_add(v___x_3359_, v_fst_3349_);
lean_dec(v_fst_3349_);
lean_dec(v___x_3359_);
v___x_3361_ = l_Char_ofNat(v___x_3360_);
lean_dec(v___x_3360_);
v___x_3362_ = lean_box_uint32(v___x_3361_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3362_);
v___x_3364_ = v___x_3352_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_snd_3350_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3364_);
v___x_3366_ = v___x_3347_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
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
lean_object* v___x_3371_; 
v___x_3371_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3307_, v_i_3310_);
lean_dec(v_i_3310_);
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
lean_dec_ref_known(v___x_3371_, 1);
v_fst_3374_ = lean_ctor_get(v_val_3373_, 0);
lean_inc(v_fst_3374_);
v_snd_3375_ = lean_ctor_get(v_val_3373_, 1);
lean_inc(v_snd_3375_);
lean_dec(v_val_3373_);
v___x_3376_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3307_, v_snd_3375_);
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
lean_object* v_val_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3399_; 
v_val_3378_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3380_ = v___x_3376_;
v_isShared_3381_ = v_isSharedCheck_3399_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_val_3378_);
lean_dec(v___x_3376_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3399_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v_fst_3382_; lean_object* v_snd_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3398_; 
v_fst_3382_ = lean_ctor_get(v_val_3378_, 0);
v_snd_3383_ = lean_ctor_get(v_val_3378_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_val_3378_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3385_ = v_val_3378_;
v_isShared_3386_ = v_isSharedCheck_3398_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_snd_3383_);
lean_inc(v_fst_3382_);
lean_dec(v_val_3378_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3398_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint32_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3387_ = lean_unsigned_to_nat(16u);
v___x_3388_ = lean_nat_mul(v___x_3387_, v_fst_3374_);
lean_dec(v_fst_3374_);
v___x_3389_ = lean_nat_add(v___x_3388_, v_fst_3382_);
lean_dec(v_fst_3382_);
lean_dec(v___x_3388_);
v___x_3390_ = l_Char_ofNat(v___x_3389_);
lean_dec(v___x_3389_);
v___x_3391_ = lean_box_uint32(v___x_3390_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3391_);
v___x_3393_ = v___x_3385_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_snd_3383_);
v___x_3393_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3395_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3393_);
v___x_3395_ = v___x_3380_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
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
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v_i_3310_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v_i_3310_);
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v_i_3310_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
return v___x_3408_;
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v_i_3310_);
v___x_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_i_3310_);
v___x_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v_i_3310_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3418_, lean_object* v_i_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Syntax_decodeQuotedChar(v_s_3418_, v_i_3419_);
lean_dec(v_i_3419_);
lean_dec_ref(v_s_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3421_){
_start:
{
uint32_t v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = 32;
v___x_3423_ = lean_uint32_dec_eq(v___y_3421_, v___x_3422_);
if (v___x_3423_ == 0)
{
uint32_t v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = 9;
v___x_3425_ = lean_uint32_dec_eq(v___y_3421_, v___x_3424_);
if (v___x_3425_ == 0)
{
uint32_t v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = 13;
v___x_3427_ = lean_uint32_dec_eq(v___y_3421_, v___x_3426_);
if (v___x_3427_ == 0)
{
uint32_t v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = 10;
v___x_3429_ = lean_uint32_dec_eq(v___y_3421_, v___x_3428_);
return v___x_3429_;
}
else
{
return v___x_3427_;
}
}
else
{
return v___x_3425_;
}
}
else
{
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3430_){
_start:
{
uint32_t v___y_270__boxed_3431_; uint8_t v_res_3432_; lean_object* v_r_3433_; 
v___y_270__boxed_3431_ = lean_unbox_uint32(v___y_3430_);
lean_dec(v___y_3430_);
v_res_3432_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_270__boxed_3431_);
v_r_3433_ = lean_box(v_res_3432_);
return v_r_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3435_, lean_object* v_i_3436_){
_start:
{
lean_object* v___f_3437_; uint32_t v___x_3442_; uint32_t v___x_3443_; uint8_t v___x_3444_; 
v___f_3437_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3442_ = lean_string_utf8_get(v_s_3435_, v_i_3436_);
v___x_3443_ = 32;
v___x_3444_ = lean_uint32_dec_eq(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
uint32_t v___x_3445_; uint8_t v___x_3446_; 
v___x_3445_ = 9;
v___x_3446_ = lean_uint32_dec_eq(v___x_3442_, v___x_3445_);
if (v___x_3446_ == 0)
{
uint32_t v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = 13;
v___x_3448_ = lean_uint32_dec_eq(v___x_3442_, v___x_3447_);
if (v___x_3448_ == 0)
{
uint32_t v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = 10;
v___x_3450_ = lean_uint32_dec_eq(v___x_3442_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_dec_ref(v_s_3435_);
v___x_3451_ = lean_box(0);
return v___x_3451_;
}
else
{
goto v___jp_3438_;
}
}
else
{
goto v___jp_3438_;
}
}
else
{
goto v___jp_3438_;
}
}
else
{
goto v___jp_3438_;
}
v___jp_3438_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = lean_string_utf8_next(v_s_3435_, v_i_3436_);
v___x_3440_ = lean_string_nextwhile(v_s_3435_, v___f_3437_, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3452_, lean_object* v_i_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Syntax_decodeStringGap(v_s_3452_, v_i_3453_);
lean_dec(v_i_3453_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3455_, lean_object* v_i_3456_, lean_object* v_acc_3457_){
_start:
{
uint32_t v_c_3458_; uint32_t v___x_3459_; uint8_t v___x_3460_; 
v_c_3458_ = lean_string_utf8_get(v_s_3455_, v_i_3456_);
v___x_3459_ = 34;
v___x_3460_ = lean_uint32_dec_eq(v_c_3458_, v___x_3459_);
if (v___x_3460_ == 0)
{
lean_object* v_i_3461_; uint8_t v___x_3462_; 
v_i_3461_ = lean_string_utf8_next(v_s_3455_, v_i_3456_);
lean_dec(v_i_3456_);
v___x_3462_ = lean_string_utf8_at_end(v_s_3455_, v_i_3461_);
if (v___x_3462_ == 0)
{
uint32_t v___x_3463_; uint8_t v___x_3464_; 
v___x_3463_ = 92;
v___x_3464_ = lean_uint32_dec_eq(v_c_3458_, v___x_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_string_push(v_acc_3457_, v_c_3458_);
v_i_3456_ = v_i_3461_;
v_acc_3457_ = v___x_3465_;
goto _start;
}
else
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Syntax_decodeQuotedChar(v_s_3455_, v_i_3461_);
if (lean_obj_tag(v___x_3467_) == 1)
{
lean_object* v_val_3468_; lean_object* v_fst_3469_; lean_object* v_snd_3470_; uint32_t v___x_3471_; lean_object* v___x_3472_; 
lean_dec(v_i_3461_);
v_val_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v_fst_3469_ = lean_ctor_get(v_val_3468_, 0);
lean_inc(v_fst_3469_);
v_snd_3470_ = lean_ctor_get(v_val_3468_, 1);
lean_inc(v_snd_3470_);
lean_dec(v_val_3468_);
v___x_3471_ = lean_unbox_uint32(v_fst_3469_);
lean_dec(v_fst_3469_);
v___x_3472_ = lean_string_push(v_acc_3457_, v___x_3471_);
v_i_3456_ = v_snd_3470_;
v_acc_3457_ = v___x_3472_;
goto _start;
}
else
{
lean_object* v___x_3474_; 
lean_dec(v___x_3467_);
lean_inc_ref(v_s_3455_);
v___x_3474_ = l_Lean_Syntax_decodeStringGap(v_s_3455_, v_i_3461_);
lean_dec(v_i_3461_);
if (lean_obj_tag(v___x_3474_) == 1)
{
lean_object* v_val_3475_; 
v_val_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_val_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v_i_3456_ = v_val_3475_;
goto _start;
}
else
{
lean_object* v___x_3477_; 
lean_dec(v___x_3474_);
lean_dec_ref(v_acc_3457_);
lean_dec_ref(v_s_3455_);
v___x_3477_ = lean_box(0);
return v___x_3477_;
}
}
}
}
else
{
lean_object* v___x_3478_; 
lean_dec(v_i_3461_);
lean_dec_ref(v_acc_3457_);
lean_dec_ref(v_s_3455_);
v___x_3478_ = lean_box(0);
return v___x_3478_;
}
}
else
{
lean_object* v___x_3479_; 
lean_dec(v_i_3456_);
lean_dec_ref(v_s_3455_);
v___x_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_acc_3457_);
return v___x_3479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3480_, lean_object* v_i_3481_, lean_object* v_num_3482_){
_start:
{
uint32_t v_c_3483_; lean_object* v_i_3484_; uint32_t v___x_3485_; uint8_t v___x_3486_; 
v_c_3483_ = lean_string_utf8_get(v_s_3480_, v_i_3481_);
v_i_3484_ = lean_string_utf8_next(v_s_3480_, v_i_3481_);
lean_dec(v_i_3481_);
v___x_3485_ = 35;
v___x_3486_ = lean_uint32_dec_eq(v_c_3483_, v___x_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3487_ = lean_string_utf8_byte_size(v_s_3480_);
v___x_3488_ = lean_unsigned_to_nat(1u);
v___x_3489_ = lean_nat_add(v_num_3482_, v___x_3488_);
lean_dec(v_num_3482_);
v___x_3490_ = lean_nat_sub(v___x_3487_, v___x_3489_);
lean_dec(v___x_3489_);
v___x_3491_ = lean_string_utf8_extract(v_s_3480_, v_i_3484_, v___x_3490_);
lean_dec(v___x_3490_);
lean_dec(v_i_3484_);
return v___x_3491_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_nat_add(v_num_3482_, v___x_3492_);
lean_dec(v_num_3482_);
v_i_3481_ = v_i_3484_;
v_num_3482_ = v___x_3493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3495_, lean_object* v_i_3496_, lean_object* v_num_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3495_, v_i_3496_, v_num_3497_);
lean_dec_ref(v_s_3495_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3499_){
_start:
{
lean_object* v___x_3500_; uint32_t v___x_3501_; uint32_t v___x_3502_; uint8_t v___x_3503_; 
v___x_3500_ = lean_unsigned_to_nat(0u);
v___x_3501_ = lean_string_utf8_get(v_s_3499_, v___x_3500_);
v___x_3502_ = 114;
v___x_3503_ = lean_uint32_dec_eq(v___x_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3506_ = l_Lean_Syntax_decodeStrLitAux(v_s_3499_, v___x_3504_, v___x_3505_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = lean_unsigned_to_nat(1u);
v___x_3508_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3499_, v___x_3507_, v___x_3500_);
lean_dec_ref(v_s_3499_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3510_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3512_ = l_Lean_Syntax_isLit_x3f(v___x_3511_, v_stx_3510_);
if (lean_obj_tag(v___x_3512_) == 1)
{
lean_object* v_val_3513_; lean_object* v___x_3514_; 
v_val_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_val_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___x_3514_ = l_Lean_Syntax_decodeStrLit(v_val_3513_);
return v___x_3514_;
}
else
{
lean_object* v___x_3515_; 
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
return v___x_3515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3516_);
lean_dec(v_stx_3516_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3518_){
_start:
{
lean_object* v___x_3519_; uint32_t v_c_3520_; uint32_t v___x_3521_; uint8_t v___x_3522_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v_c_3520_ = lean_string_utf8_get(v_s_3518_, v___x_3519_);
v___x_3521_ = 92;
v___x_3522_ = lean_uint32_dec_eq(v_c_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = lean_box_uint32(v_c_3520_);
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_unsigned_to_nat(2u);
v___x_3526_ = l_Lean_Syntax_decodeQuotedChar(v_s_3518_, v___x_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_box(0);
return v___x_3527_;
}
else
{
lean_object* v_val_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3536_; 
v_val_3528_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3530_ = v___x_3526_;
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_val_3528_);
lean_dec(v___x_3526_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_fst_3532_; lean_object* v___x_3534_; 
v_fst_3532_ = lean_ctor_get(v_val_3528_, 0);
lean_inc(v_fst_3532_);
lean_dec(v_val_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v_fst_3532_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_fst_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Syntax_decodeCharLit(v_s_3537_);
lean_dec_ref(v_s_3537_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3539_){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3541_ = l_Lean_Syntax_isLit_x3f(v___x_3540_, v_stx_3539_);
if (lean_obj_tag(v___x_3541_) == 1)
{
lean_object* v_val_3542_; lean_object* v___x_3543_; 
v_val_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_val_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = l_Lean_Syntax_decodeCharLit(v_val_3542_);
lean_dec(v_val_3542_);
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; 
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
return v___x_3544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3545_);
lean_dec(v_stx_3545_);
return v_res_3546_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3547_){
_start:
{
uint32_t v___x_3569_; uint8_t v___x_3570_; 
v___x_3569_ = 65;
v___x_3570_ = lean_uint32_dec_le(v___x_3569_, v___y_3547_);
if (v___x_3570_ == 0)
{
goto v___jp_3564_;
}
else
{
uint32_t v___x_3571_; uint8_t v___x_3572_; 
v___x_3571_ = 90;
v___x_3572_ = lean_uint32_dec_le(v___y_3547_, v___x_3571_);
if (v___x_3572_ == 0)
{
goto v___jp_3564_;
}
else
{
return v___x_3572_;
}
}
v___jp_3548_:
{
uint32_t v___x_3549_; uint8_t v___x_3550_; 
v___x_3549_ = 95;
v___x_3550_ = lean_uint32_dec_eq(v___y_3547_, v___x_3549_);
if (v___x_3550_ == 0)
{
uint32_t v___x_3551_; uint8_t v___x_3552_; 
v___x_3551_ = 39;
v___x_3552_ = lean_uint32_dec_eq(v___y_3547_, v___x_3551_);
if (v___x_3552_ == 0)
{
uint32_t v___x_3553_; uint8_t v___x_3554_; 
v___x_3553_ = 33;
v___x_3554_ = lean_uint32_dec_eq(v___y_3547_, v___x_3553_);
if (v___x_3554_ == 0)
{
uint32_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3555_ = 63;
v___x_3556_ = lean_uint32_dec_eq(v___y_3547_, v___x_3555_);
if (v___x_3556_ == 0)
{
uint8_t v___x_3557_; 
v___x_3557_ = l_Lean_isLetterLike(v___y_3547_);
if (v___x_3557_ == 0)
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Lean_isSubScriptAlnum(v___y_3547_);
return v___x_3558_;
}
else
{
return v___x_3557_;
}
}
else
{
return v___x_3556_;
}
}
else
{
return v___x_3554_;
}
}
else
{
return v___x_3552_;
}
}
else
{
return v___x_3550_;
}
}
v___jp_3559_:
{
uint32_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = 48;
v___x_3561_ = lean_uint32_dec_le(v___x_3560_, v___y_3547_);
if (v___x_3561_ == 0)
{
goto v___jp_3548_;
}
else
{
uint32_t v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = 57;
v___x_3563_ = lean_uint32_dec_le(v___y_3547_, v___x_3562_);
if (v___x_3563_ == 0)
{
goto v___jp_3548_;
}
else
{
return v___x_3563_;
}
}
}
v___jp_3564_:
{
uint32_t v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = 97;
v___x_3566_ = lean_uint32_dec_le(v___x_3565_, v___y_3547_);
if (v___x_3566_ == 0)
{
goto v___jp_3559_;
}
else
{
uint32_t v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = 122;
v___x_3568_ = lean_uint32_dec_le(v___y_3547_, v___x_3567_);
if (v___x_3568_ == 0)
{
goto v___jp_3559_;
}
else
{
return v___x_3568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3573_){
_start:
{
uint32_t v___y_513__boxed_3574_; uint8_t v_res_3575_; lean_object* v_r_3576_; 
v___y_513__boxed_3574_ = lean_unbox_uint32(v___y_3573_);
lean_dec(v___y_3573_);
v_res_3575_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_513__boxed_3574_);
v_r_3576_ = lean_box(v_res_3575_);
return v_r_3576_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3577_, uint32_t v___x_3578_, uint32_t v___y_3579_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_uint32_dec_le(v___x_3577_, v___y_3579_);
if (v___x_3580_ == 0)
{
return v___x_3580_;
}
else
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_uint32_dec_le(v___y_3579_, v___x_3578_);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3582_, lean_object* v___x_3583_, lean_object* v___y_3584_){
_start:
{
uint32_t v___x_566__boxed_3585_; uint32_t v___x_567__boxed_3586_; uint32_t v___y_568__boxed_3587_; uint8_t v_res_3588_; lean_object* v_r_3589_; 
v___x_566__boxed_3585_ = lean_unbox_uint32(v___x_3582_);
lean_dec(v___x_3582_);
v___x_567__boxed_3586_ = lean_unbox_uint32(v___x_3583_);
lean_dec(v___x_3583_);
v___y_568__boxed_3587_ = lean_unbox_uint32(v___y_3584_);
lean_dec(v___y_3584_);
v_res_3588_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_566__boxed_3585_, v___x_567__boxed_3586_, v___y_568__boxed_3587_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3590_, uint8_t v___x_3591_, uint32_t v_x_3592_){
_start:
{
uint32_t v___x_3593_; uint8_t v___x_3594_; 
v___x_3593_ = 187;
v___x_3594_ = lean_uint32_dec_eq(v_x_3592_, v___x_3593_);
if (v___x_3594_ == 0)
{
return v___x_3590_;
}
else
{
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3595_, lean_object* v___x_3596_, lean_object* v_x_3597_){
_start:
{
uint8_t v___x_579__boxed_3598_; uint8_t v___x_580__boxed_3599_; uint32_t v_x_581__boxed_3600_; uint8_t v_res_3601_; lean_object* v_r_3602_; 
v___x_579__boxed_3598_ = lean_unbox(v___x_3595_);
v___x_580__boxed_3599_ = lean_unbox(v___x_3596_);
v_x_581__boxed_3600_ = lean_unbox_uint32(v_x_3597_);
lean_dec(v_x_3597_);
v_res_3601_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_579__boxed_3598_, v___x_580__boxed_3599_, v_x_581__boxed_3600_);
v_r_3602_ = lean_box(v_res_3601_);
return v_r_3602_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = 48;
v___x_3605_ = lean_box_uint32(v___x_3604_);
return v___x_3605_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = 57;
v___x_3607_ = lean_box_uint32(v___x_3606_);
return v___x_3607_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___f_3610_; 
v___x_3608_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3609_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3610_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3610_, 0, v___x_3608_);
lean_closure_set(v___f_3610_, 1, v___x_3609_);
return v___f_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3611_, lean_object* v_acc_3612_){
_start:
{
lean_object* v_ss_3614_; lean_object* v_acc_3615_; uint8_t v___x_3624_; 
lean_inc_ref(v_ss_3611_);
v___x_3624_ = lean_substring_isempty(v_ss_3611_);
if (v___x_3624_ == 0)
{
uint32_t v_curr_3625_; uint32_t v___x_3626_; uint8_t v___x_3627_; 
lean_inc_ref(v_ss_3611_);
v_curr_3625_ = lean_substring_front(v_ss_3611_);
v___x_3626_ = 171;
v___x_3627_ = lean_uint32_dec_eq(v_curr_3625_, v___x_3626_);
if (v___x_3627_ == 0)
{
lean_object* v___f_3628_; uint32_t v___x_3664_; uint8_t v___x_3665_; 
v___f_3628_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3664_ = 65;
v___x_3665_ = lean_uint32_dec_le(v___x_3664_, v_curr_3625_);
if (v___x_3665_ == 0)
{
goto v___jp_3659_;
}
else
{
uint32_t v___x_3666_; uint8_t v___x_3667_; 
v___x_3666_ = 90;
v___x_3667_ = lean_uint32_dec_le(v_curr_3625_, v___x_3666_);
if (v___x_3667_ == 0)
{
goto v___jp_3659_;
}
else
{
goto v___jp_3629_;
}
}
v___jp_3629_:
{
lean_object* v_idPart_3630_; lean_object* v_startPos_3631_; lean_object* v_stopPos_3632_; lean_object* v_startPos_3633_; lean_object* v_stopPos_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_inc_ref(v_ss_3611_);
v_idPart_3630_ = lean_substring_takewhile(v_ss_3611_, v___f_3628_);
v_startPos_3631_ = lean_ctor_get(v_idPart_3630_, 1);
v_stopPos_3632_ = lean_ctor_get(v_idPart_3630_, 2);
v_startPos_3633_ = lean_ctor_get(v_ss_3611_, 1);
v_stopPos_3634_ = lean_ctor_get(v_ss_3611_, 2);
v___x_3635_ = lean_nat_sub(v_stopPos_3632_, v_startPos_3631_);
v___x_3636_ = lean_nat_sub(v_stopPos_3634_, v_startPos_3633_);
v___x_3637_ = lean_substring_extract(v_ss_3611_, v___x_3635_, v___x_3636_);
v___x_3638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_idPart_3630_);
lean_ctor_set(v___x_3638_, 1, v_acc_3612_);
v_ss_3614_ = v___x_3637_;
v_acc_3615_ = v___x_3638_;
goto v___jp_3613_;
}
v___jp_3639_:
{
uint32_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = 95;
v___x_3641_ = lean_uint32_dec_eq(v_curr_3625_, v___x_3640_);
if (v___x_3641_ == 0)
{
uint8_t v___x_3642_; 
v___x_3642_ = l_Lean_isLetterLike(v_curr_3625_);
if (v___x_3642_ == 0)
{
uint32_t v___x_3643_; uint8_t v___x_3644_; 
v___x_3643_ = 48;
v___x_3644_ = lean_uint32_dec_le(v___x_3643_, v_curr_3625_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; 
lean_dec(v_acc_3612_);
lean_dec_ref(v_ss_3611_);
v___x_3645_ = lean_box(0);
return v___x_3645_;
}
else
{
uint32_t v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = 57;
v___x_3647_ = lean_uint32_dec_le(v_curr_3625_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; 
lean_dec(v_acc_3612_);
lean_dec_ref(v_ss_3611_);
v___x_3648_ = lean_box(0);
return v___x_3648_;
}
else
{
lean_object* v___f_3649_; lean_object* v_idPart_3650_; lean_object* v_startPos_3651_; lean_object* v_stopPos_3652_; lean_object* v_startPos_3653_; lean_object* v_stopPos_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___f_3649_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3611_);
v_idPart_3650_ = lean_substring_takewhile(v_ss_3611_, v___f_3649_);
v_startPos_3651_ = lean_ctor_get(v_idPart_3650_, 1);
v_stopPos_3652_ = lean_ctor_get(v_idPart_3650_, 2);
v_startPos_3653_ = lean_ctor_get(v_ss_3611_, 1);
v_stopPos_3654_ = lean_ctor_get(v_ss_3611_, 2);
v___x_3655_ = lean_nat_sub(v_stopPos_3652_, v_startPos_3651_);
v___x_3656_ = lean_nat_sub(v_stopPos_3654_, v_startPos_3653_);
v___x_3657_ = lean_substring_extract(v_ss_3611_, v___x_3655_, v___x_3656_);
v___x_3658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3658_, 0, v_idPart_3650_);
lean_ctor_set(v___x_3658_, 1, v_acc_3612_);
v_ss_3614_ = v___x_3657_;
v_acc_3615_ = v___x_3658_;
goto v___jp_3613_;
}
}
}
else
{
goto v___jp_3629_;
}
}
else
{
goto v___jp_3629_;
}
}
v___jp_3659_:
{
uint32_t v___x_3660_; uint8_t v___x_3661_; 
v___x_3660_ = 97;
v___x_3661_ = lean_uint32_dec_le(v___x_3660_, v_curr_3625_);
if (v___x_3661_ == 0)
{
goto v___jp_3639_;
}
else
{
uint32_t v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = 122;
v___x_3663_ = lean_uint32_dec_le(v_curr_3625_, v___x_3662_);
if (v___x_3663_ == 0)
{
goto v___jp_3639_;
}
else
{
goto v___jp_3629_;
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___f_3670_; lean_object* v_escapedPart_3671_; lean_object* v_str_3672_; lean_object* v_startPos_3673_; lean_object* v_stopPos_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3694_; 
v___x_3668_ = lean_box(v___x_3627_);
v___x_3669_ = lean_box(v___x_3624_);
v___f_3670_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3670_, 0, v___x_3668_);
lean_closure_set(v___f_3670_, 1, v___x_3669_);
lean_inc_ref(v_ss_3611_);
v_escapedPart_3671_ = lean_substring_takewhile(v_ss_3611_, v___f_3670_);
v_str_3672_ = lean_ctor_get(v_escapedPart_3671_, 0);
v_startPos_3673_ = lean_ctor_get(v_escapedPart_3671_, 1);
v_stopPos_3674_ = lean_ctor_get(v_escapedPart_3671_, 2);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_escapedPart_3671_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3676_ = v_escapedPart_3671_;
v_isShared_3677_ = v_isSharedCheck_3694_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_stopPos_3674_);
lean_inc(v_startPos_3673_);
lean_inc(v_str_3672_);
lean_dec(v_escapedPart_3671_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3694_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_startPos_3678_; lean_object* v_stopPos_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v_escapedPart_3683_; 
v_startPos_3678_ = lean_ctor_get(v_ss_3611_, 1);
v_stopPos_3679_ = lean_ctor_get(v_ss_3611_, 2);
v___x_3680_ = lean_string_utf8_next(v_str_3672_, v_stopPos_3674_);
lean_dec(v_stopPos_3674_);
lean_inc(v_stopPos_3679_);
v___x_3681_ = lean_string_pos_min(v_stopPos_3679_, v___x_3680_);
lean_inc(v___x_3681_);
lean_inc(v_startPos_3673_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 2, v___x_3681_);
v_escapedPart_3683_ = v___x_3676_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_str_3672_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_startPos_3673_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v___x_3681_);
v_escapedPart_3683_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; uint32_t v___x_3686_; uint32_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3684_ = lean_nat_sub(v___x_3681_, v_startPos_3673_);
lean_dec(v_startPos_3673_);
lean_dec(v___x_3681_);
lean_inc(v___x_3684_);
lean_inc_ref_n(v_escapedPart_3683_, 2);
v___x_3685_ = lean_substring_prev(v_escapedPart_3683_, v___x_3684_);
v___x_3686_ = lean_substring_get(v_escapedPart_3683_, v___x_3685_);
v___x_3687_ = 187;
v___x_3688_ = lean_uint32_dec_eq(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; 
lean_dec(v___x_3684_);
lean_dec_ref(v_escapedPart_3683_);
lean_dec(v_acc_3612_);
lean_dec_ref(v_ss_3611_);
v___x_3689_ = lean_box(0);
return v___x_3689_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_nat_sub(v_stopPos_3679_, v_startPos_3678_);
v___x_3691_ = lean_substring_extract(v_ss_3611_, v___x_3684_, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_escapedPart_3683_);
lean_ctor_set(v___x_3692_, 1, v_acc_3612_);
v_ss_3614_ = v___x_3691_;
v_acc_3615_ = v___x_3692_;
goto v___jp_3613_;
}
}
}
}
}
else
{
lean_object* v___x_3695_; 
lean_dec(v_acc_3612_);
lean_dec_ref(v_ss_3611_);
v___x_3695_ = lean_box(0);
return v___x_3695_;
}
v___jp_3613_:
{
uint32_t v___x_3616_; uint32_t v___x_3617_; uint8_t v___x_3618_; 
lean_inc_ref(v_ss_3614_);
v___x_3616_ = lean_substring_front(v_ss_3614_);
v___x_3617_ = 46;
v___x_3618_ = lean_uint32_dec_eq(v___x_3616_, v___x_3617_);
if (v___x_3618_ == 0)
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_substring_isempty(v_ss_3614_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; 
lean_dec(v_acc_3615_);
v___x_3620_ = lean_box(0);
return v___x_3620_;
}
else
{
return v_acc_3615_;
}
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = lean_unsigned_to_nat(1u);
v___x_3622_ = lean_substring_drop(v_ss_3614_, v___x_3621_);
v_ss_3611_ = v___x_3622_;
v_acc_3612_ = v_acc_3615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = lean_box(0);
v___x_3698_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3696_, v___x_3697_);
v___x_3699_ = l_List_reverse___redArg(v___x_3698_);
return v___x_3699_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3704_ = lean_unsigned_to_nat(10u);
v___x_3705_ = lean_unsigned_to_nat(1265u);
v___x_3706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3708_ = l_mkPanicMessageWithDecl(v___x_3707_, v___x_3706_, v___x_3705_, v___x_3704_, v___x_3703_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(lean_object* v_as_3709_, size_t v_i_3710_, size_t v_stop_3711_, lean_object* v_b_3712_){
_start:
{
uint8_t v___x_3713_; 
v___x_3713_ = lean_usize_dec_eq(v_i_3710_, v_stop_3711_);
if (v___x_3713_ == 0)
{
size_t v___x_3714_; size_t v___x_3715_; lean_object* v___x_3716_; lean_object* v_comp_3717_; uint32_t v___x_3718_; uint32_t v___x_3719_; uint8_t v___x_3720_; 
v___x_3714_ = ((size_t)1ULL);
v___x_3715_ = lean_usize_sub(v_i_3710_, v___x_3714_);
v___x_3716_ = lean_array_uget_borrowed(v_as_3709_, v___x_3715_);
lean_inc(v___x_3716_);
v_comp_3717_ = lean_substring_tostring(v___x_3716_);
lean_inc_ref(v_comp_3717_);
v___x_3718_ = lean_string_front(v_comp_3717_);
v___x_3719_ = 171;
v___x_3720_ = lean_uint32_dec_eq(v___x_3718_, v___x_3719_);
if (v___x_3720_ == 0)
{
uint32_t v___x_3721_; uint8_t v___x_3722_; 
v___x_3721_ = 48;
v___x_3722_ = lean_uint32_dec_le(v___x_3721_, v___x_3718_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_Name_str___override(v_b_3712_, v_comp_3717_);
v_i_3710_ = v___x_3715_;
v_b_3712_ = v___x_3723_;
goto _start;
}
else
{
uint32_t v___x_3725_; uint8_t v___x_3726_; 
v___x_3725_ = 57;
v___x_3726_ = lean_uint32_dec_le(v___x_3718_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_Name_str___override(v_b_3712_, v_comp_3717_);
v_i_3710_ = v___x_3715_;
v_b_3712_ = v___x_3727_;
goto _start;
}
else
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3717_);
lean_dec_ref(v_comp_3717_);
if (lean_obj_tag(v___x_3729_) == 1)
{
lean_object* v_val_3730_; lean_object* v___x_3731_; 
v_val_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_val_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = l_Lean_Name_num___override(v_b_3712_, v_val_3730_);
v_i_3710_ = v___x_3715_;
v_b_3712_ = v___x_3731_;
goto _start;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec(v___x_3729_);
lean_dec(v_b_3712_);
v___x_3733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3734_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3733_);
v_i_3710_ = v___x_3715_;
v_b_3712_ = v___x_3734_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3736_ = lean_unsigned_to_nat(1u);
v___x_3737_ = lean_string_drop(v_comp_3717_, v___x_3736_);
v___x_3738_ = lean_string_dropright(v___x_3737_, v___x_3736_);
v___x_3739_ = l_Lean_Name_str___override(v_b_3712_, v___x_3738_);
v_i_3710_ = v___x_3715_;
v_b_3712_ = v___x_3739_;
goto _start;
}
}
else
{
return v_b_3712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_as_3741_, lean_object* v_i_3742_, lean_object* v_stop_3743_, lean_object* v_b_3744_){
_start:
{
size_t v_i_boxed_3745_; size_t v_stop_boxed_3746_; lean_object* v_res_3747_; 
v_i_boxed_3745_ = lean_unbox_usize(v_i_3742_);
lean_dec(v_i_3742_);
v_stop_boxed_3746_ = lean_unbox_usize(v_stop_3743_);
lean_dec(v_stop_3743_);
v_res_3747_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(v_as_3741_, v_i_boxed_3745_, v_stop_boxed_3746_, v_b_3744_);
lean_dec_ref(v_as_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3748_){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = lean_box(0);
v___x_3750_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3748_, v___x_3749_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_box(0);
return v___x_3751_;
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = lean_array_mk(v___x_3750_);
v___x_3754_ = lean_array_get_size(v___x_3753_);
v___x_3755_ = lean_unsigned_to_nat(0u);
v___x_3756_ = lean_nat_dec_lt(v___x_3755_, v___x_3754_);
if (v___x_3756_ == 0)
{
lean_dec_ref(v___x_3753_);
return v___x_3752_;
}
else
{
size_t v___x_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_usize_of_nat(v___x_3754_);
v___x_3758_ = ((size_t)0ULL);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Substring_Raw_toName_spec__0(v___x_3753_, v___x_3757_, v___x_3758_, v___x_3752_);
lean_dec_ref(v___x_3753_);
return v___x_3759_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3760_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_string_utf8_byte_size(v_s_3760_);
v___x_3763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3763_, 0, v_s_3760_);
lean_ctor_set(v___x_3763_, 1, v___x_3761_);
lean_ctor_set(v___x_3763_, 2, v___x_3762_);
v___x_3764_ = l_Substring_Raw_toName(v___x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3765_){
_start:
{
lean_object* v___x_3766_; uint32_t v___x_3767_; uint32_t v___x_3768_; uint8_t v___x_3769_; 
v___x_3766_ = lean_unsigned_to_nat(0u);
v___x_3767_ = lean_string_utf8_get(v_s_3765_, v___x_3766_);
v___x_3768_ = 96;
v___x_3769_ = lean_uint32_dec_eq(v___x_3767_, v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
lean_dec_ref(v_s_3765_);
v___x_3770_ = lean_box(0);
return v___x_3770_;
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3771_ = lean_string_utf8_byte_size(v_s_3765_);
v___x_3772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3772_, 0, v_s_3765_);
lean_ctor_set(v___x_3772_, 1, v___x_3766_);
lean_ctor_set(v___x_3772_, 2, v___x_3771_);
v___x_3773_ = lean_unsigned_to_nat(1u);
v___x_3774_ = lean_substring_drop(v___x_3772_, v___x_3773_);
v___x_3775_ = l_Substring_Raw_toName(v___x_3774_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_box(0);
return v___x_3776_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
return v___x_3777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3778_){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3780_ = l_Lean_Syntax_isLit_x3f(v___x_3779_, v_stx_3778_);
if (lean_obj_tag(v___x_3780_) == 1)
{
lean_object* v_val_3781_; lean_object* v___x_3782_; 
v_val_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_val_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3782_ = l_Lean_Syntax_decodeNameLit(v_val_3781_);
return v___x_3782_;
}
else
{
lean_object* v___x_3783_; 
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
return v___x_3783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3784_);
lean_dec(v_stx_3784_);
return v_res_3785_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3786_){
_start:
{
if (lean_obj_tag(v_x_3786_) == 1)
{
lean_object* v_args_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_args_3787_ = lean_ctor_get(v_x_3786_, 2);
v___x_3788_ = lean_unsigned_to_nat(0u);
v___x_3789_ = lean_array_get_size(v_args_3787_);
v___x_3790_ = lean_nat_dec_lt(v___x_3788_, v___x_3789_);
return v___x_3790_;
}
else
{
uint8_t v___x_3791_; 
v___x_3791_ = 0;
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3792_){
_start:
{
uint8_t v_res_3793_; lean_object* v_r_3794_; 
v_res_3793_ = l_Lean_Syntax_hasArgs(v_x_3792_);
lean_dec(v_x_3792_);
v_r_3794_ = lean_box(v_res_3793_);
return v_r_3794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3795_){
_start:
{
if (lean_obj_tag(v_x_3795_) == 2)
{
uint8_t v___x_3796_; 
v___x_3796_ = 1;
return v___x_3796_;
}
else
{
uint8_t v___x_3797_; 
v___x_3797_ = 0;
return v___x_3797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3798_){
_start:
{
uint8_t v_res_3799_; lean_object* v_r_3800_; 
v_res_3799_ = l_Lean_Syntax_isAtom(v_x_3798_);
lean_dec(v_x_3798_);
v_r_3800_ = lean_box(v_res_3799_);
return v_r_3800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3801_, lean_object* v_x_3802_){
_start:
{
if (lean_obj_tag(v_x_3802_) == 2)
{
lean_object* v_val_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v_val_3803_ = lean_ctor_get(v_x_3802_, 1);
lean_inc_ref(v_val_3803_);
lean_dec_ref_known(v_x_3802_, 2);
v___x_3804_ = lean_string_trim(v_val_3803_);
v___x_3805_ = lean_string_trim(v_token_3801_);
v___x_3806_ = lean_string_dec_eq(v___x_3804_, v___x_3805_);
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3804_);
return v___x_3806_;
}
else
{
uint8_t v___x_3807_; 
lean_dec(v_x_3802_);
lean_dec_ref(v_token_3801_);
v___x_3807_ = 0;
return v___x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3808_, lean_object* v_x_3809_){
_start:
{
uint8_t v_res_3810_; lean_object* v_r_3811_; 
v_res_3810_ = l_Lean_Syntax_isToken(v_token_3808_, v_x_3809_);
v_r_3811_ = lean_box(v_res_3810_);
return v_r_3811_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3812_){
_start:
{
switch(lean_obj_tag(v_stx_3812_))
{
case 1:
{
lean_object* v_kind_3813_; lean_object* v_args_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_kind_3813_ = lean_ctor_get(v_stx_3812_, 1);
v_args_3814_ = lean_ctor_get(v_stx_3812_, 2);
v___x_3815_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3816_ = lean_name_eq(v_kind_3813_, v___x_3815_);
if (v___x_3816_ == 0)
{
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3817_ = lean_array_get_size(v_args_3814_);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = lean_nat_dec_eq(v___x_3817_, v___x_3818_);
return v___x_3819_;
}
}
case 0:
{
uint8_t v___x_3820_; 
v___x_3820_ = 1;
return v___x_3820_;
}
default: 
{
uint8_t v___x_3821_; 
v___x_3821_ = 0;
return v___x_3821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3822_){
_start:
{
uint8_t v_res_3823_; lean_object* v_r_3824_; 
v_res_3823_ = l_Lean_Syntax_isNone(v_stx_3822_);
lean_dec(v_stx_3822_);
v_r_3824_ = lean_box(v_res_3823_);
return v_r_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3825_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_Syntax_getOptional_x3f(v_stx_3825_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_box(0);
return v___x_3827_;
}
else
{
lean_object* v_val_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3836_; 
v_val_3828_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3830_ = v___x_3826_;
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_val_3828_);
lean_dec(v___x_3826_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = l_Lean_Syntax_getId(v_val_3828_);
lean_dec(v_val_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3832_);
v___x_3834_ = v___x_3830_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3837_);
lean_dec(v_stx_3837_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3839_, lean_object* v_x_3840_){
_start:
{
if (lean_obj_tag(v_x_3840_) == 1)
{
lean_object* v_args_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v_args_3841_ = lean_ctor_get(v_x_3840_, 2);
lean_inc_ref(v_p_3839_);
lean_inc_ref(v_x_3840_);
v___x_3842_ = lean_apply_1(v_p_3839_, v_x_3840_);
v___x_3843_ = lean_unbox(v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3845_; size_t v_sz_3846_; size_t v___x_3847_; lean_object* v___x_3848_; lean_object* v_fst_3849_; 
lean_inc_ref(v_args_3841_);
lean_dec_ref_known(v_x_3840_, 3);
v___x_3844_ = lean_box(0);
v___x_3845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3846_ = lean_array_size(v_args_3841_);
v___x_3847_ = ((size_t)0ULL);
v___x_3848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3839_, v_args_3841_, v_sz_3846_, v___x_3847_, v___x_3845_);
lean_dec_ref(v_args_3841_);
v_fst_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_fst_3849_);
lean_dec_ref(v___x_3848_);
if (lean_obj_tag(v_fst_3849_) == 0)
{
return v___x_3844_;
}
else
{
lean_object* v_val_3850_; 
v_val_3850_ = lean_ctor_get(v_fst_3849_, 0);
lean_inc(v_val_3850_);
lean_dec_ref_known(v_fst_3849_, 1);
return v_val_3850_;
}
}
else
{
lean_object* v___x_3851_; 
lean_dec_ref(v_p_3839_);
v___x_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_x_3840_);
return v___x_3851_;
}
}
else
{
lean_object* v___x_3852_; uint8_t v___x_3853_; 
lean_inc(v_x_3840_);
v___x_3852_ = lean_apply_1(v_p_3839_, v_x_3840_);
v___x_3853_ = lean_unbox(v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; 
lean_dec(v_x_3840_);
v___x_3854_ = lean_box(0);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_x_3840_);
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3856_, lean_object* v_as_3857_, size_t v_sz_3858_, size_t v_i_3859_, lean_object* v_b_3860_){
_start:
{
uint8_t v___x_3861_; 
v___x_3861_ = lean_usize_dec_lt(v_i_3859_, v_sz_3858_);
if (v___x_3861_ == 0)
{
lean_dec_ref(v_p_3856_);
lean_inc_ref(v_b_3860_);
return v_b_3860_;
}
else
{
lean_object* v___x_3862_; lean_object* v_a_3863_; lean_object* v___x_3864_; 
v___x_3862_ = lean_box(0);
v_a_3863_ = lean_array_uget_borrowed(v_as_3857_, v_i_3859_);
lean_inc(v_a_3863_);
lean_inc_ref(v_p_3856_);
v___x_3864_ = l_Lean_Syntax_findAux(v_p_3856_, v_a_3863_);
if (lean_obj_tag(v___x_3864_) == 1)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec_ref(v_p_3856_);
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
lean_ctor_set(v___x_3866_, 1, v___x_3862_);
return v___x_3866_;
}
else
{
lean_object* v___x_3867_; size_t v___x_3868_; size_t v___x_3869_; 
lean_dec(v___x_3864_);
v___x_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3868_ = ((size_t)1ULL);
v___x_3869_ = lean_usize_add(v_i_3859_, v___x_3868_);
v_i_3859_ = v___x_3869_;
v_b_3860_ = v___x_3867_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3871_, lean_object* v_as_3872_, lean_object* v_sz_3873_, lean_object* v_i_3874_, lean_object* v_b_3875_){
_start:
{
size_t v_sz_boxed_3876_; size_t v_i_boxed_3877_; lean_object* v_res_3878_; 
v_sz_boxed_3876_ = lean_unbox_usize(v_sz_3873_);
lean_dec(v_sz_3873_);
v_i_boxed_3877_ = lean_unbox_usize(v_i_3874_);
lean_dec(v_i_3874_);
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3871_, v_as_3872_, v_sz_boxed_3876_, v_i_boxed_3877_, v_b_3875_);
lean_dec_ref(v_b_3875_);
lean_dec_ref(v_as_3872_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3879_, lean_object* v_p_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_Syntax_findAux(v_p_3880_, v_stx_3879_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Syntax_isNatLit_x3f(v_s_3882_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_unsigned_to_nat(0u);
return v___x_3884_;
}
else
{
lean_object* v_val_3885_; 
v_val_3885_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_val_3885_);
lean_dec_ref_known(v___x_3883_, 1);
return v_val_3885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_TSyntax_getNat(v_s_3886_);
lean_dec(v_s_3886_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3891_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3893_ = l_Lean_Syntax_isLit_x3f(v___x_3892_, v_stx_3891_);
if (lean_obj_tag(v___x_3893_) == 1)
{
lean_object* v_val_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_val_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3895_ = lean_unsigned_to_nat(0u);
v___x_3896_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3894_, v___x_3895_, v___x_3895_);
lean_dec(v_val_3894_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; 
lean_dec(v___x_3893_);
v___x_3897_ = lean_box(0);
return v___x_3897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3898_);
lean_dec(v_stx_3898_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3900_){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_unsigned_to_nat(0u);
return v___x_3902_;
}
else
{
lean_object* v_val_3903_; 
v_val_3903_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_val_3903_);
lean_dec_ref_known(v___x_3901_, 1);
return v_val_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_TSyntax_getHexNumVal(v_s_3904_);
lean_dec(v_s_3904_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3906_, lean_object* v_p_3907_, lean_object* v_n_3908_){
_start:
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_string_utf8_at_end(v_s_3906_, v_p_3907_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; uint32_t v___x_3911_; uint32_t v___x_3912_; uint8_t v___x_3913_; 
v___x_3910_ = lean_string_utf8_next(v_s_3906_, v_p_3907_);
v___x_3911_ = lean_string_utf8_get(v_s_3906_, v_p_3907_);
lean_dec(v_p_3907_);
v___x_3912_ = 95;
v___x_3913_ = lean_uint32_dec_eq(v___x_3911_, v___x_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_nat_add(v_n_3908_, v___x_3914_);
lean_dec(v_n_3908_);
v_p_3907_ = v___x_3910_;
v_n_3908_ = v___x_3915_;
goto _start;
}
else
{
v_p_3907_ = v___x_3910_;
goto _start;
}
}
else
{
lean_dec(v_p_3907_);
return v_n_3908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3918_, lean_object* v_p_3919_, lean_object* v_n_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3918_, v_p_3919_, v_n_3920_);
lean_dec_ref(v_s_3918_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3922_){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3924_ = l_Lean_Syntax_isLit_x3f(v___x_3923_, v_s_3922_);
if (lean_obj_tag(v___x_3924_) == 1)
{
lean_object* v_val_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_val_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_val_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3925_, v___x_3926_, v___x_3926_);
lean_dec(v_val_3925_);
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; 
lean_dec(v___x_3924_);
v___x_3928_ = lean_unsigned_to_nat(0u);
return v___x_3928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_TSyntax_getHexNumSize(v_s_3929_);
lean_dec(v_s_3929_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Syntax_getId(v_s_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_TSyntax_getId(v_s_3933_);
lean_dec(v_s_3933_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3942_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3942_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3944_;
}
else
{
lean_object* v_val_3945_; 
v_val_3945_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v___x_3943_, 1);
return v_val_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_TSyntax_getScientific(v_s_3946_);
lean_dec(v_s_3946_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Syntax_isStrLit_x3f(v_s_3948_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3950_;
}
else
{
lean_object* v_val_3951_; 
v_val_3951_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v___x_3949_, 1);
return v_val_3951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_TSyntax_getString(v_s_3952_);
lean_dec(v_s_3952_);
return v_res_3953_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_Syntax_isCharLit_x3f(v_s_3954_);
if (lean_obj_tag(v___x_3955_) == 0)
{
uint32_t v___x_3956_; 
v___x_3956_ = 65;
return v___x_3956_;
}
else
{
lean_object* v_val_3957_; uint32_t v___x_3958_; 
v_val_3957_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_val_3957_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3958_ = lean_unbox_uint32(v_val_3957_);
lean_dec(v_val_3957_);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3959_){
_start:
{
uint32_t v_res_3960_; lean_object* v_r_3961_; 
v_res_3960_ = l_Lean_TSyntax_getChar(v_s_3959_);
lean_dec(v_s_3959_);
v_r_3961_ = lean_box_uint32(v_res_3960_);
return v_r_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Syntax_isNameLit_x3f(v_s_3962_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_box(0);
return v___x_3964_;
}
else
{
lean_object* v_val_3965_; 
v_val_3965_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_val_3965_);
lean_dec_ref_known(v___x_3963_, 1);
return v_val_3965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_TSyntax_getName(v_s_3966_);
lean_dec(v_s_3966_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3968_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = lean_unsigned_to_nat(0u);
v___x_3970_ = l_Lean_Syntax_getArg(v_s_3968_, v___x_3969_);
v___x_3971_ = l_Lean_Syntax_getId(v___x_3970_);
lean_dec(v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_TSyntax_getHygieneInfo(v_s_3972_);
lean_dec(v_s_3972_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3974_, v_a_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3977_, v_a_3978_);
lean_dec_ref(v_a_3978_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3980_){
_start:
{
lean_object* v___f_3981_; 
v___f_3981_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3981_, 0, v_sep_3980_);
return v___f_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3982_, lean_object* v_sep_3983_){
_start:
{
lean_object* v___f_3984_; 
v___f_3984_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3984_, 0, v_sep_3983_);
return v___f_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3985_, lean_object* v_sep_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3985_, v_sep_3986_);
lean_dec(v_k_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3988_, lean_object* v_val_3989_, uint8_t v_canonical_3990_){
_start:
{
lean_object* v___x_3991_; lean_object* v_src_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_imported_3995_; lean_object* v_ctx_3996_; lean_object* v_scopes_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4013_; 
v___x_3991_ = lean_unsigned_to_nat(0u);
v_src_3992_ = l_Lean_Syntax_getArg(v_s_3988_, v___x_3991_);
v___x_3993_ = l_Lean_Syntax_getId(v_src_3992_);
v___x_3994_ = l_Lean_extractMacroScopes(v___x_3993_);
v_imported_3995_ = lean_ctor_get(v___x_3994_, 1);
v_ctx_3996_ = lean_ctor_get(v___x_3994_, 2);
v_scopes_3997_ = lean_ctor_get(v___x_3994_, 3);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; 
v_unused_4014_ = lean_ctor_get(v___x_3994_, 0);
lean_dec(v_unused_4014_);
v___x_3999_ = v___x_3994_;
v_isShared_4000_ = v_isSharedCheck_4013_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_scopes_3997_);
lean_inc(v_ctx_3996_);
lean_inc(v_imported_3995_);
lean_dec(v___x_3994_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4013_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = l_Lean_Name_eraseMacroScopes(v_val_3989_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4001_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_imported_3995_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_ctx_3996_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_scopes_3997_);
v___x_4003_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v_id_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_id_4004_ = l_Lean_MacroScopesView_review(v___x_4003_);
v___x_4005_ = l_Lean_SourceInfo_fromRef(v_src_3992_, v_canonical_3990_);
lean_dec(v_src_3992_);
v___x_4006_ = 1;
v___x_4007_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3989_, v___x_4006_);
v___x_4008_ = lean_string_utf8_byte_size(v___x_4007_);
v___x_4009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_3991_);
lean_ctor_set(v___x_4009_, 2, v___x_4008_);
v___x_4010_ = lean_box(0);
v___x_4011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4005_);
lean_ctor_set(v___x_4011_, 1, v___x_4009_);
lean_ctor_set(v___x_4011_, 2, v_id_4004_);
lean_ctor_set(v___x_4011_, 3, v___x_4010_);
return v___x_4011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4015_, lean_object* v_val_4016_, lean_object* v_canonical_4017_){
_start:
{
uint8_t v_canonical_boxed_4018_; lean_object* v_res_4019_; 
v_canonical_boxed_4018_ = lean_unbox(v_canonical_4017_);
v_res_4019_ = l_Lean_HygieneInfo_mkIdent(v_s_4015_, v_val_4016_, v_canonical_boxed_4018_);
lean_dec(v_s_4015_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4020_, lean_object* v_inst_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_apply_1(v_inst_4020_, v_a_4022_);
v___x_4024_ = lean_apply_1(v_inst_4021_, v___x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4025_, lean_object* v_inst_4026_){
_start:
{
lean_object* v___f_4027_; 
v___f_4027_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4027_, 0, v_inst_4025_);
lean_closure_set(v___f_4027_, 1, v_inst_4026_);
return v___f_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4028_, lean_object* v_k_4029_, lean_object* v_k_x27_4030_, lean_object* v_inst_4031_, lean_object* v_inst_4032_){
_start:
{
lean_object* v___f_4033_; 
v___f_4033_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4033_, 0, v_inst_4031_);
lean_closure_set(v___f_4033_, 1, v_inst_4032_);
return v___f_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4034_, lean_object* v_k_4035_, lean_object* v_k_x27_4036_, lean_object* v_inst_4037_, lean_object* v_inst_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4034_, v_k_4035_, v_k_x27_4036_, v_inst_4037_, v_inst_4038_);
lean_dec(v_k_x27_4036_);
lean_dec(v_k_4035_);
return v_res_4039_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4048_ = l_Lean_mkCIdent(v___x_4047_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4054_ = l_Lean_mkCIdent(v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4055_){
_start:
{
if (v_x_4055_ == 0)
{
lean_object* v___x_4056_; 
v___x_4056_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4056_;
}
else
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4058_){
_start:
{
uint8_t v_x_85__boxed_4059_; lean_object* v_res_4060_; 
v_x_85__boxed_4059_ = lean_unbox(v_x_4058_);
v_res_4060_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4059_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4063_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_box(2);
v___x_4065_ = l_Lean_Syntax_mkCharLit(v_val_4063_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4066_){
_start:
{
uint32_t v_val_boxed_4067_; lean_object* v_res_4068_; 
v_val_boxed_4067_ = lean_unbox_uint32(v_val_4066_);
lean_dec(v_val_4066_);
v_res_4068_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4067_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_box(2);
v___x_4073_ = l_Lean_Syntax_mkStrLit(v_val_4071_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4076_){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = l_Nat_reprFast(v_n_4076_);
v___x_4078_ = lean_box(2);
v___x_4079_ = l_Lean_Syntax_mkNumLit(v___x_4077_, v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4088_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4089_ = lean_substring_tostring(v_s_4087_);
v___x_4090_ = lean_box(2);
v___x_4091_ = l_Lean_Syntax_mkStrLit(v___x_4089_, v___x_4090_);
v___x_4092_ = lean_unsigned_to_nat(1u);
v___x_4093_ = lean_mk_empty_array_with_capacity(v___x_4092_);
v___x_4094_ = lean_array_push(v___x_4093_, v___x_4091_);
v___x_4095_ = l_Lean_Syntax_mkCApp(v___x_4088_, v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4098_, lean_object* v_x_4099_){
_start:
{
switch(lean_obj_tag(v_x_4099_))
{
case 0:
{
uint8_t v___x_4100_; 
v___x_4100_ = l_List_isEmpty___redArg(v_acc_4098_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; 
v___x_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4101_, 0, v_acc_4098_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; 
lean_dec(v_acc_4098_);
v___x_4102_ = lean_box(0);
return v___x_4102_;
}
}
case 1:
{
lean_object* v_pre_4103_; lean_object* v_str_4104_; lean_object* v_val_4106_; lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v_pre_4103_ = lean_ctor_get(v_x_4099_, 0);
lean_inc(v_pre_4103_);
v_str_4104_ = lean_ctor_get(v_x_4099_, 1);
lean_inc_ref(v_str_4104_);
lean_dec_ref_known(v_x_4099_, 2);
v___x_4109_ = lean_unsigned_to_nat(0u);
v___x_4110_ = lean_string_utf8_byte_size(v_str_4104_);
v___x_4111_ = lean_nat_dec_lt(v___x_4109_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4112_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4113_ = lean_string_append(v___x_4112_, v_str_4104_);
lean_dec_ref(v_str_4104_);
v___x_4114_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4115_ = lean_string_append(v___x_4113_, v___x_4114_);
v_val_4106_ = v___x_4115_;
goto v___jp_4105_;
}
else
{
lean_object* v___f_4116_; lean_object* v___f_4124_; uint32_t v___y_4131_; uint32_t v___y_4136_; uint8_t v_c_4150_; uint8_t v___x_4159_; uint8_t v___x_4160_; 
v___f_4116_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4124_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4150_ = lean_string_get_byte_fast(v_str_4104_, v___x_4109_);
v___x_4159_ = 97;
v___x_4160_ = lean_uint8_dec_le(v___x_4159_, v_c_4150_);
if (v___x_4160_ == 0)
{
goto v___jp_4154_;
}
else
{
uint8_t v___x_4161_; uint8_t v___x_4162_; 
v___x_4161_ = 122;
v___x_4162_ = lean_uint8_dec_le(v_c_4150_, v___x_4161_);
if (v___x_4162_ == 0)
{
goto v___jp_4154_;
}
else
{
goto v___jp_4147_;
}
}
v___jp_4117_:
{
uint8_t v___x_4118_; 
lean_inc_ref(v_str_4104_);
v___x_4118_ = lean_string_any(v_str_4104_, v___f_4116_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4119_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4120_ = lean_string_append(v___x_4119_, v_str_4104_);
lean_dec_ref(v_str_4104_);
v___x_4121_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4122_ = lean_string_append(v___x_4120_, v___x_4121_);
v_val_4106_ = v___x_4122_;
goto v___jp_4105_;
}
else
{
lean_object* v___x_4123_; 
lean_dec_ref(v_str_4104_);
lean_dec(v_pre_4103_);
lean_dec(v_acc_4098_);
v___x_4123_ = lean_box(0);
return v___x_4123_;
}
}
v___jp_4125_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
lean_inc_ref(v_str_4104_);
v___x_4126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4126_, 0, v_str_4104_);
lean_ctor_set(v___x_4126_, 1, v___x_4109_);
lean_ctor_set(v___x_4126_, 2, v___x_4110_);
v___x_4127_ = lean_unsigned_to_nat(1u);
v___x_4128_ = lean_substring_drop(v___x_4126_, v___x_4127_);
v___x_4129_ = lean_substring_all(v___x_4128_, v___f_4124_);
if (v___x_4129_ == 0)
{
goto v___jp_4117_;
}
else
{
v_val_4106_ = v_str_4104_;
goto v___jp_4105_;
}
}
v___jp_4130_:
{
uint32_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = 95;
v___x_4133_ = lean_uint32_dec_eq(v___y_4131_, v___x_4132_);
if (v___x_4133_ == 0)
{
uint8_t v___x_4134_; 
v___x_4134_ = l_Lean_isLetterLike(v___y_4131_);
if (v___x_4134_ == 0)
{
goto v___jp_4117_;
}
else
{
goto v___jp_4125_;
}
}
else
{
goto v___jp_4125_;
}
}
v___jp_4135_:
{
uint32_t v___x_4137_; uint8_t v___x_4138_; 
v___x_4137_ = 97;
v___x_4138_ = lean_uint32_dec_le(v___x_4137_, v___y_4136_);
if (v___x_4138_ == 0)
{
v___y_4131_ = v___y_4136_;
goto v___jp_4130_;
}
else
{
uint32_t v___x_4139_; uint8_t v___x_4140_; 
v___x_4139_ = 122;
v___x_4140_ = lean_uint32_dec_le(v___y_4136_, v___x_4139_);
if (v___x_4140_ == 0)
{
v___y_4131_ = v___y_4136_;
goto v___jp_4130_;
}
else
{
goto v___jp_4125_;
}
}
}
v___jp_4141_:
{
uint32_t v___x_4142_; uint32_t v___x_4143_; uint8_t v___x_4144_; 
v___x_4142_ = lean_string_utf8_get(v_str_4104_, v___x_4109_);
v___x_4143_ = 65;
v___x_4144_ = lean_uint32_dec_le(v___x_4143_, v___x_4142_);
if (v___x_4144_ == 0)
{
v___y_4136_ = v___x_4142_;
goto v___jp_4135_;
}
else
{
uint32_t v___x_4145_; uint8_t v___x_4146_; 
v___x_4145_ = 90;
v___x_4146_ = lean_uint32_dec_le(v___x_4142_, v___x_4145_);
if (v___x_4146_ == 0)
{
v___y_4136_ = v___x_4142_;
goto v___jp_4135_;
}
else
{
goto v___jp_4125_;
}
}
}
v___jp_4147_:
{
lean_object* v___x_4148_; uint8_t v___x_4149_; 
v___x_4148_ = lean_unsigned_to_nat(1u);
v___x_4149_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4104_, v___x_4148_);
if (v___x_4149_ == 0)
{
goto v___jp_4141_;
}
else
{
v_val_4106_ = v_str_4104_;
goto v___jp_4105_;
}
}
v___jp_4151_:
{
uint8_t v___x_4152_; uint8_t v___x_4153_; 
v___x_4152_ = 95;
v___x_4153_ = lean_uint8_dec_eq(v_c_4150_, v___x_4152_);
if (v___x_4153_ == 0)
{
goto v___jp_4141_;
}
else
{
goto v___jp_4147_;
}
}
v___jp_4154_:
{
uint8_t v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = 65;
v___x_4156_ = lean_uint8_dec_le(v___x_4155_, v_c_4150_);
if (v___x_4156_ == 0)
{
goto v___jp_4151_;
}
else
{
uint8_t v___x_4157_; uint8_t v___x_4158_; 
v___x_4157_ = 90;
v___x_4158_ = lean_uint8_dec_le(v_c_4150_, v___x_4157_);
if (v___x_4158_ == 0)
{
goto v___jp_4151_;
}
else
{
goto v___jp_4147_;
}
}
}
}
v___jp_4105_:
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4107_, 0, v_val_4106_);
lean_ctor_set(v___x_4107_, 1, v_acc_4098_);
v_acc_4098_ = v___x_4107_;
v_x_4099_ = v_pre_4103_;
goto _start;
}
}
default: 
{
lean_object* v___x_4163_; 
lean_dec_ref_known(v_x_4099_, 2);
lean_dec(v_acc_4098_);
v___x_4163_ = lean_box(0);
return v___x_4163_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4171_ = l_Lean_mkCIdent(v___x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4182_){
_start:
{
switch(lean_obj_tag(v_x_4182_))
{
case 0:
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4183_;
}
case 1:
{
lean_object* v_pre_4184_; lean_object* v_str_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v_pre_4184_ = lean_ctor_get(v_x_4182_, 0);
lean_inc(v_pre_4184_);
v_str_4185_ = lean_ctor_get(v_x_4182_, 1);
lean_inc_ref(v_str_4185_);
lean_dec_ref_known(v_x_4182_, 2);
v___x_4186_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4187_ = l_Lean_quoteNameMk(v_pre_4184_);
v___x_4188_ = lean_box(2);
v___x_4189_ = l_Lean_Syntax_mkStrLit(v_str_4185_, v___x_4188_);
v___x_4190_ = lean_unsigned_to_nat(2u);
v___x_4191_ = lean_mk_empty_array_with_capacity(v___x_4190_);
v___x_4192_ = lean_array_push(v___x_4191_, v___x_4187_);
v___x_4193_ = lean_array_push(v___x_4192_, v___x_4189_);
v___x_4194_ = l_Lean_Syntax_mkCApp(v___x_4186_, v___x_4193_);
return v___x_4194_;
}
default: 
{
lean_object* v_pre_4195_; lean_object* v_i_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_pre_4195_ = lean_ctor_get(v_x_4182_, 0);
lean_inc(v_pre_4195_);
v_i_4196_ = lean_ctor_get(v_x_4182_, 1);
lean_inc(v_i_4196_);
lean_dec_ref_known(v_x_4182_, 2);
v___x_4197_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4198_ = l_Lean_quoteNameMk(v_pre_4195_);
v___x_4199_ = l_Nat_reprFast(v_i_4196_);
v___x_4200_ = lean_box(2);
v___x_4201_ = l_Lean_Syntax_mkNumLit(v___x_4199_, v___x_4200_);
v___x_4202_ = lean_unsigned_to_nat(2u);
v___x_4203_ = lean_mk_empty_array_with_capacity(v___x_4202_);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4198_);
v___x_4205_ = lean_array_push(v___x_4204_, v___x_4201_);
v___x_4206_ = l_Lean_Syntax_mkCApp(v___x_4197_, v___x_4205_);
return v___x_4206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4213_){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_box(0);
lean_inc(v_n_4213_);
v___x_4215_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4214_, v_n_4213_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_quoteNameMk(v_n_4213_);
return v___x_4216_;
}
else
{
lean_object* v_val_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_dec(v_n_4213_);
v_val_4217_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_val_4217_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4218_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4219_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4220_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4221_ = lean_string_intercalate(v___x_4220_, v_val_4217_);
v___x_4222_ = lean_string_append(v___x_4219_, v___x_4221_);
lean_dec_ref(v___x_4221_);
v___x_4223_ = lean_box(2);
v___x_4224_ = l_Lean_Syntax_mkNameLit(v___x_4222_, v___x_4223_);
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_mk_empty_array_with_capacity(v___x_4225_);
v___x_4227_ = lean_array_push(v___x_4226_, v___x_4224_);
v___x_4228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4223_);
lean_ctor_set(v___x_4228_, 1, v___x_4218_);
lean_ctor_set(v___x_4228_, 2, v___x_4227_);
return v___x_4228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4229_){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_box(0);
lean_inc(v_n_4229_);
v___x_4231_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4230_, v_n_4229_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_quoteNameMk(v_n_4229_);
return v___x_4232_;
}
else
{
lean_object* v_val_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
lean_dec(v_n_4229_);
v_val_4233_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_val_4233_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4234_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4235_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4236_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4237_ = lean_string_intercalate(v___x_4236_, v_val_4233_);
v___x_4238_ = lean_string_append(v___x_4235_, v___x_4237_);
lean_dec_ref(v___x_4237_);
v___x_4239_ = lean_box(2);
v___x_4240_ = l_Lean_Syntax_mkNameLit(v___x_4238_, v___x_4239_);
v___x_4241_ = lean_unsigned_to_nat(1u);
v___x_4242_ = lean_mk_empty_array_with_capacity(v___x_4241_);
v___x_4243_ = lean_array_push(v___x_4242_, v___x_4240_);
v___x_4244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4239_);
lean_ctor_set(v___x_4244_, 1, v___x_4234_);
lean_ctor_set(v___x_4244_, 2, v___x_4243_);
return v___x_4244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4252_, lean_object* v_inst_4253_, lean_object* v_x_4254_){
_start:
{
lean_object* v_fst_4255_; lean_object* v_snd_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_fst_4255_ = lean_ctor_get(v_x_4254_, 0);
lean_inc(v_fst_4255_);
v_snd_4256_ = lean_ctor_get(v_x_4254_, 1);
lean_inc(v_snd_4256_);
lean_dec_ref(v_x_4254_);
v___x_4257_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4258_ = lean_apply_1(v_inst_4252_, v_fst_4255_);
v___x_4259_ = lean_apply_1(v_inst_4253_, v_snd_4256_);
v___x_4260_ = lean_unsigned_to_nat(2u);
v___x_4261_ = lean_mk_empty_array_with_capacity(v___x_4260_);
v___x_4262_ = lean_array_push(v___x_4261_, v___x_4258_);
v___x_4263_ = lean_array_push(v___x_4262_, v___x_4259_);
v___x_4264_ = l_Lean_Syntax_mkCApp(v___x_4257_, v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4265_, lean_object* v_inst_4266_){
_start:
{
lean_object* v___f_4267_; 
v___f_4267_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4267_, 0, v_inst_4265_);
lean_closure_set(v___f_4267_, 1, v_inst_4266_);
return v___f_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4268_, lean_object* v_00_u03b2_4269_, lean_object* v_inst_4270_, lean_object* v_inst_4271_){
_start:
{
lean_object* v___f_4272_; 
v___f_4272_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4272_, 0, v_inst_4270_);
lean_closure_set(v___f_4272_, 1, v_inst_4271_);
return v___f_4272_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4278_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4279_ = l_Lean_mkCIdent(v___x_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4284_, lean_object* v_x_4285_){
_start:
{
if (lean_obj_tag(v_x_4285_) == 0)
{
lean_object* v___x_4286_; 
lean_dec_ref(v_inst_4284_);
v___x_4286_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4286_;
}
else
{
lean_object* v_head_4287_; lean_object* v_tail_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v_head_4287_ = lean_ctor_get(v_x_4285_, 0);
lean_inc(v_head_4287_);
v_tail_4288_ = lean_ctor_get(v_x_4285_, 1);
lean_inc(v_tail_4288_);
lean_dec_ref_known(v_x_4285_, 2);
v___x_4289_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4284_);
v___x_4290_ = lean_apply_1(v_inst_4284_, v_head_4287_);
v___x_4291_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4284_, v_tail_4288_);
v___x_4292_ = lean_unsigned_to_nat(2u);
v___x_4293_ = lean_mk_empty_array_with_capacity(v___x_4292_);
v___x_4294_ = lean_array_push(v___x_4293_, v___x_4290_);
v___x_4295_ = lean_array_push(v___x_4294_, v___x_4291_);
v___x_4296_ = l_Lean_Syntax_mkCApp(v___x_4289_, v___x_4295_);
return v___x_4296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4297_, lean_object* v_inst_4298_, lean_object* v_x_4299_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4298_, v_x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4301_, v_a_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4304_, lean_object* v_inst_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4305_, v_a_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4309_, 0, lean_box(0));
lean_closure_set(v___x_4309_, 1, v_inst_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4310_, lean_object* v_inst_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4312_, 0, lean_box(0));
lean_closure_set(v___x_4312_, 1, v_inst_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4315_, lean_object* v_xs_4316_, lean_object* v_i_4317_, lean_object* v_args_4318_){
_start:
{
lean_object* v___x_4319_; uint8_t v___x_4320_; 
v___x_4319_ = lean_array_get_size(v_xs_4316_);
v___x_4320_ = lean_nat_dec_lt(v_i_4317_, v___x_4319_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
lean_dec(v_i_4317_);
lean_dec_ref(v_inst_4315_);
v___x_4321_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4322_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4323_ = l_Nat_reprFast(v___x_4319_);
v___x_4324_ = lean_string_append(v___x_4322_, v___x_4323_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = l_Lean_Name_mkStr2(v___x_4321_, v___x_4324_);
v___x_4326_ = l_Lean_Syntax_mkCApp(v___x_4325_, v_args_4318_);
return v___x_4326_;
}
else
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4327_ = lean_unsigned_to_nat(1u);
v___x_4328_ = lean_nat_add(v_i_4317_, v___x_4327_);
v___x_4329_ = lean_array_fget_borrowed(v_xs_4316_, v_i_4317_);
lean_dec(v_i_4317_);
lean_inc_ref(v_inst_4315_);
lean_inc(v___x_4329_);
v___x_4330_ = lean_apply_1(v_inst_4315_, v___x_4329_);
v___x_4331_ = lean_array_push(v_args_4318_, v___x_4330_);
v_i_4317_ = v___x_4328_;
v_args_4318_ = v___x_4331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4333_, lean_object* v_xs_4334_, lean_object* v_i_4335_, lean_object* v_args_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4333_, v_xs_4334_, v_i_4335_, v_args_4336_);
lean_dec_ref(v_xs_4334_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4338_, lean_object* v_inst_4339_, lean_object* v_xs_4340_, lean_object* v_i_4341_, lean_object* v_args_4342_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4339_, v_xs_4340_, v_i_4341_, v_args_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4344_, lean_object* v_inst_4345_, lean_object* v_xs_4346_, lean_object* v_i_4347_, lean_object* v_args_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4344_, v_inst_4345_, v_xs_4346_, v_i_4347_, v_args_4348_);
lean_dec_ref(v_xs_4346_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4354_, lean_object* v_xs_4355_){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4356_ = lean_array_get_size(v_xs_4355_);
v___x_4357_ = lean_unsigned_to_nat(8u);
v___x_4358_ = lean_nat_dec_le(v___x_4356_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4359_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4360_ = lean_array_to_list(v_xs_4355_);
v___x_4361_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4354_, v___x_4360_);
v___x_4362_ = lean_unsigned_to_nat(1u);
v___x_4363_ = lean_mk_empty_array_with_capacity(v___x_4362_);
v___x_4364_ = lean_array_push(v___x_4363_, v___x_4361_);
v___x_4365_ = l_Lean_Syntax_mkCApp(v___x_4359_, v___x_4364_);
return v___x_4365_;
}
else
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4368_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4354_, v_xs_4355_, v___x_4366_, v___x_4367_);
lean_dec_ref(v_xs_4355_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4369_, lean_object* v_inst_4370_, lean_object* v_xs_4371_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4370_, v_xs_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4373_, lean_object* v_xs_4374_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4373_, v_xs_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4376_, lean_object* v_inst_4377_, lean_object* v_xs_4378_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4377_, v_xs_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4380_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4381_, 0, lean_box(0));
lean_closure_set(v___x_4381_, 1, v_inst_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4382_, lean_object* v_inst_4383_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4384_, 0, lean_box(0));
lean_closure_set(v___x_4384_, 1, v_inst_4383_);
return v___x_4384_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4391_ = l_Lean_mkIdent(v___x_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4396_, lean_object* v_x_4397_){
_start:
{
if (lean_obj_tag(v_x_4397_) == 0)
{
lean_object* v___x_4398_; 
lean_dec_ref(v_inst_4396_);
v___x_4398_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4398_;
}
else
{
lean_object* v_val_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_val_4399_ = lean_ctor_get(v_x_4397_, 0);
lean_inc(v_val_4399_);
lean_dec_ref_known(v_x_4397_, 1);
v___x_4400_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4401_ = lean_apply_1(v_inst_4396_, v_val_4399_);
v___x_4402_ = lean_unsigned_to_nat(1u);
v___x_4403_ = lean_mk_empty_array_with_capacity(v___x_4402_);
v___x_4404_ = lean_array_push(v___x_4403_, v___x_4401_);
v___x_4405_ = l_Lean_Syntax_mkCApp(v___x_4400_, v___x_4404_);
return v___x_4405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4406_){
_start:
{
lean_object* v___f_4407_; 
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4407_, 0, v_inst_4406_);
return v___f_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4408_, lean_object* v_inst_4409_){
_start:
{
lean_object* v___f_4410_; 
v___f_4410_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4410_, 0, v_inst_4409_);
return v___f_4410_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(lean_object* v_k_4411_){
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
uint8_t v___x_4415_; 
v___x_4415_ = 0;
return v___x_4415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v_k_4416_){
_start:
{
uint8_t v_res_4417_; lean_object* v_r_4418_; 
v_res_4417_ = l_Lean_evalPrec___lam__0(v_k_4416_);
lean_dec(v_k_4416_);
v_r_4418_ = lean_box(v_res_4417_);
return v_r_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_methods_4424_; lean_object* v_quotContext_4425_; lean_object* v_currMacroScope_4426_; lean_object* v_currRecDepth_4427_; lean_object* v_maxRecDepth_4428_; lean_object* v_ref_4429_; lean_object* v___f_4430_; lean_object* v_methods_4432_; lean_object* v_quotContext_4433_; lean_object* v_currMacroScope_4434_; lean_object* v_currRecDepth_4435_; lean_object* v_maxRecDepth_4436_; lean_object* v_ref_4437_; lean_object* v___y_4438_; lean_object* v___x_4466_; uint8_t v___x_4467_; 
v_methods_4424_ = lean_ctor_get(v_a_4422_, 0);
v_quotContext_4425_ = lean_ctor_get(v_a_4422_, 1);
v_currMacroScope_4426_ = lean_ctor_get(v_a_4422_, 2);
v_currRecDepth_4427_ = lean_ctor_get(v_a_4422_, 3);
v_maxRecDepth_4428_ = lean_ctor_get(v_a_4422_, 4);
v_ref_4429_ = lean_ctor_get(v_a_4422_, 5);
v___f_4430_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4466_ = lean_unsigned_to_nat(0u);
v___x_4467_ = lean_nat_dec_eq(v_maxRecDepth_4428_, v___x_4466_);
if (v___x_4467_ == 0)
{
uint8_t v___x_4468_; 
v___x_4468_ = lean_nat_dec_eq(v_currRecDepth_4427_, v_maxRecDepth_4428_);
if (v___x_4468_ == 0)
{
v_methods_4432_ = v_methods_4424_;
v_quotContext_4433_ = v_quotContext_4425_;
v_currMacroScope_4434_ = v_currMacroScope_4426_;
v_currRecDepth_4435_ = v_currRecDepth_4427_;
v_maxRecDepth_4436_ = v_maxRecDepth_4428_;
v_ref_4437_ = v_ref_4429_;
v___y_4438_ = v_a_4423_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v_stx_4421_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
lean_ctor_set(v___x_4471_, 1, v_a_4423_);
return v___x_4471_;
}
}
else
{
v_methods_4432_ = v_methods_4424_;
v_quotContext_4433_ = v_quotContext_4425_;
v_currMacroScope_4434_ = v_currMacroScope_4426_;
v_currRecDepth_4435_ = v_currRecDepth_4427_;
v_maxRecDepth_4436_ = v_maxRecDepth_4428_;
v_ref_4437_ = v_ref_4429_;
v___y_4438_ = v_a_4423_;
goto v___jp_4431_;
}
v___jp_4431_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4439_ = lean_unsigned_to_nat(1u);
v___x_4440_ = lean_nat_add(v_currRecDepth_4435_, v___x_4439_);
lean_inc(v_ref_4437_);
lean_inc(v_maxRecDepth_4436_);
lean_inc(v_currMacroScope_4434_);
lean_inc(v_quotContext_4433_);
lean_inc(v_methods_4432_);
v___x_4441_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4441_, 0, v_methods_4432_);
lean_ctor_set(v___x_4441_, 1, v_quotContext_4433_);
lean_ctor_set(v___x_4441_, 2, v_currMacroScope_4434_);
lean_ctor_set(v___x_4441_, 3, v___x_4440_);
lean_ctor_set(v___x_4441_, 4, v_maxRecDepth_4436_);
lean_ctor_set(v___x_4441_, 5, v_ref_4437_);
lean_inc_ref(v___x_4441_);
v___x_4442_ = l_Lean_expandMacros(v_stx_4421_, v___f_4430_, v___x_4441_, v___y_4438_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4456_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
v_a_4444_ = lean_ctor_get(v___x_4442_, 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4446_ = v___x_4442_;
v_isShared_4447_ = v_isSharedCheck_4456_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_inc(v_a_4443_);
lean_dec(v___x_4442_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4456_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4448_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4443_);
v___x_4449_ = l_Lean_Syntax_isOfKind(v_a_4443_, v___x_4448_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_del_object(v___x_4446_);
v___x_4450_ = ((lean_object*)(l_Lean_evalPrec___closed__1));
v___x_4451_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4443_, v___x_4450_, v___x_4441_, v_a_4444_);
lean_dec_ref_known(v___x_4441_, 6);
lean_dec(v_a_4443_);
return v___x_4451_;
}
else
{
lean_object* v___x_4452_; lean_object* v___x_4454_; 
lean_dec_ref_known(v___x_4441_, 6);
v___x_4452_ = l_Lean_TSyntax_getNat(v_a_4443_);
lean_dec(v_a_4443_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 0, v___x_4452_);
v___x_4454_ = v___x_4446_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4455_, 1, v_a_4444_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec_ref_known(v___x_4441_, 6);
v_a_4457_ = lean_ctor_get(v___x_4442_, 0);
v_a_4458_ = lean_ctor_get(v___x_4442_, 1);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4442_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_inc(v_a_4457_);
lean_dec(v___x_4442_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4457_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Lean_evalPrec(v_stx_4472_, v_a_4473_, v_a_4474_);
lean_dec_ref(v_a_4473_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_methods_4480_; lean_object* v_quotContext_4481_; lean_object* v_currMacroScope_4482_; lean_object* v_currRecDepth_4483_; lean_object* v_maxRecDepth_4484_; lean_object* v_ref_4485_; lean_object* v___f_4486_; lean_object* v_methods_4488_; lean_object* v_quotContext_4489_; lean_object* v_currMacroScope_4490_; lean_object* v_currRecDepth_4491_; lean_object* v_maxRecDepth_4492_; lean_object* v_ref_4493_; lean_object* v___y_4494_; lean_object* v___x_4522_; uint8_t v___x_4523_; 
v_methods_4480_ = lean_ctor_get(v_a_4478_, 0);
v_quotContext_4481_ = lean_ctor_get(v_a_4478_, 1);
v_currMacroScope_4482_ = lean_ctor_get(v_a_4478_, 2);
v_currRecDepth_4483_ = lean_ctor_get(v_a_4478_, 3);
v_maxRecDepth_4484_ = lean_ctor_get(v_a_4478_, 4);
v_ref_4485_ = lean_ctor_get(v_a_4478_, 5);
v___f_4486_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = lean_nat_dec_eq(v_maxRecDepth_4484_, v___x_4522_);
if (v___x_4523_ == 0)
{
uint8_t v___x_4524_; 
v___x_4524_ = lean_nat_dec_eq(v_currRecDepth_4483_, v_maxRecDepth_4484_);
if (v___x_4524_ == 0)
{
v_methods_4488_ = v_methods_4480_;
v_quotContext_4489_ = v_quotContext_4481_;
v_currMacroScope_4490_ = v_currMacroScope_4482_;
v_currRecDepth_4491_ = v_currRecDepth_4483_;
v_maxRecDepth_4492_ = v_maxRecDepth_4484_;
v_ref_4493_ = v_ref_4485_;
v___y_4494_ = v_a_4479_;
goto v___jp_4487_;
}
else
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4526_, 0, v_stx_4477_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
lean_ctor_set(v___x_4527_, 1, v_a_4479_);
return v___x_4527_;
}
}
else
{
v_methods_4488_ = v_methods_4480_;
v_quotContext_4489_ = v_quotContext_4481_;
v_currMacroScope_4490_ = v_currMacroScope_4482_;
v_currRecDepth_4491_ = v_currRecDepth_4483_;
v_maxRecDepth_4492_ = v_maxRecDepth_4484_;
v_ref_4493_ = v_ref_4485_;
v___y_4494_ = v_a_4479_;
goto v___jp_4487_;
}
v___jp_4487_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4495_ = lean_unsigned_to_nat(1u);
v___x_4496_ = lean_nat_add(v_currRecDepth_4491_, v___x_4495_);
lean_inc(v_ref_4493_);
lean_inc(v_maxRecDepth_4492_);
lean_inc(v_currMacroScope_4490_);
lean_inc(v_quotContext_4489_);
lean_inc(v_methods_4488_);
v___x_4497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4497_, 0, v_methods_4488_);
lean_ctor_set(v___x_4497_, 1, v_quotContext_4489_);
lean_ctor_set(v___x_4497_, 2, v_currMacroScope_4490_);
lean_ctor_set(v___x_4497_, 3, v___x_4496_);
lean_ctor_set(v___x_4497_, 4, v_maxRecDepth_4492_);
lean_ctor_set(v___x_4497_, 5, v_ref_4493_);
lean_inc_ref(v___x_4497_);
v___x_4498_ = l_Lean_expandMacros(v_stx_4477_, v___f_4486_, v___x_4497_, v___y_4494_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4512_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
v_a_4500_ = lean_ctor_get(v___x_4498_, 1);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4502_ = v___x_4498_;
v_isShared_4503_ = v_isSharedCheck_4512_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_inc(v_a_4499_);
lean_dec(v___x_4498_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4512_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4499_);
v___x_4505_ = l_Lean_Syntax_isOfKind(v_a_4499_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
lean_del_object(v___x_4502_);
v___x_4506_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4507_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4499_, v___x_4506_, v___x_4497_, v_a_4500_);
lean_dec_ref_known(v___x_4497_, 6);
lean_dec(v_a_4499_);
return v___x_4507_;
}
else
{
lean_object* v___x_4508_; lean_object* v___x_4510_; 
lean_dec_ref_known(v___x_4497_, 6);
v___x_4508_ = l_Lean_TSyntax_getNat(v_a_4499_);
lean_dec(v_a_4499_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4508_);
v___x_4510_ = v___x_4502_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_a_4500_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec_ref_known(v___x_4497_, 6);
v_a_4513_ = lean_ctor_get(v___x_4498_, 0);
v_a_4514_ = lean_ctor_get(v___x_4498_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4498_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_inc(v_a_4513_);
lean_dec(v___x_4498_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4513_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_a_4514_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_evalPrio(v_stx_4528_, v_a_4529_, v_a_4530_);
lean_dec_ref(v_a_4529_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
if (lean_obj_tag(v_x_4532_) == 0)
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = lean_unsigned_to_nat(1000u);
v___x_4536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
lean_ctor_set(v___x_4536_, 1, v_a_4534_);
return v___x_4536_;
}
else
{
lean_object* v_val_4537_; lean_object* v___x_4538_; 
v_val_4537_ = lean_ctor_get(v_x_4532_, 0);
lean_inc(v_val_4537_);
lean_dec_ref_known(v_x_4532_, 1);
v___x_4538_ = l_Lean_evalPrio(v_val_4537_, v_a_4533_, v_a_4534_);
return v___x_4538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_evalOptPrio(v_x_4539_, v_a_4540_, v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4543_, lean_object* v_x1_4544_, lean_object* v_x2_4545_){
_start:
{
lean_object* v_fst_4546_; uint8_t v___x_4547_; 
v_fst_4546_ = lean_ctor_get(v_x1_4544_, 0);
v___x_4547_ = lean_unbox(v_fst_4546_);
if (v___x_4547_ == 0)
{
lean_object* v_snd_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v_x2_4545_);
v_snd_4548_ = lean_ctor_get(v_x1_4544_, 1);
v_isSharedCheck_4556_ = !lean_is_exclusive(v_x1_4544_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; 
v_unused_4557_ = lean_ctor_get(v_x1_4544_, 0);
lean_dec(v_unused_4557_);
v___x_4550_ = v_x1_4544_;
v_isShared_4551_ = v_isSharedCheck_4556_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_snd_4548_);
lean_dec(v_x1_4544_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4556_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4554_; 
v___x_4552_ = lean_box(v___x_4543_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4552_);
v___x_4554_ = v___x_4550_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4552_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_snd_4548_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
else
{
lean_object* v_snd_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4568_; 
v_snd_4558_ = lean_ctor_get(v_x1_4544_, 1);
v_isSharedCheck_4568_ = !lean_is_exclusive(v_x1_4544_);
if (v_isSharedCheck_4568_ == 0)
{
lean_object* v_unused_4569_; 
v_unused_4569_ = lean_ctor_get(v_x1_4544_, 0);
lean_dec(v_unused_4569_);
v___x_4560_ = v_x1_4544_;
v_isShared_4561_ = v_isSharedCheck_4568_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_snd_4558_);
lean_dec(v_x1_4544_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4568_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
uint8_t v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4566_; 
v___x_4562_ = 0;
v___x_4563_ = lean_array_push(v_snd_4558_, v_x2_4545_);
v___x_4564_ = lean_box(v___x_4562_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 1, v___x_4563_);
lean_ctor_set(v___x_4560_, 0, v___x_4564_);
v___x_4566_ = v___x_4560_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4564_);
lean_ctor_set(v_reuseFailAlloc_4567_, 1, v___x_4563_);
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
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4570_, lean_object* v_x1_4571_, lean_object* v_x2_4572_){
_start:
{
uint8_t v___x_87__boxed_4573_; lean_object* v_res_4574_; 
v___x_87__boxed_4573_ = lean_unbox(v___x_4570_);
v_res_4574_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4573_, v_x1_4571_, v_x2_4572_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4596_){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; 
v___x_4597_ = lean_unsigned_to_nat(0u);
v___x_4598_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4599_ = lean_array_get_size(v_as_4596_);
v___x_4600_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4601_ = lean_nat_dec_lt(v___x_4597_, v___x_4599_);
if (v___x_4601_ == 0)
{
lean_dec_ref(v_as_4596_);
return v___x_4598_;
}
else
{
lean_object* v___x_4602_; lean_object* v___f_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; size_t v___x_4606_; size_t v___x_4607_; lean_object* v___x_4608_; lean_object* v_snd_4609_; 
v___x_4602_ = lean_box(v___x_4601_);
v___f_4603_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4603_, 0, v___x_4602_);
v___x_4604_ = lean_box(v___x_4601_);
v___x_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
lean_ctor_set(v___x_4605_, 1, v___x_4598_);
v___x_4606_ = ((size_t)0ULL);
v___x_4607_ = lean_usize_of_nat(v___x_4599_);
v___x_4608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4600_, v___f_4603_, v_as_4596_, v___x_4606_, v___x_4607_, v___x_4605_);
v_snd_4609_ = lean_ctor_get(v___x_4608_, 1);
lean_inc(v_snd_4609_);
lean_dec(v___x_4608_);
return v_snd_4609_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4610_, lean_object* v_as_4611_){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; uint8_t v___x_4616_; 
v___x_4612_ = lean_unsigned_to_nat(0u);
v___x_4613_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4614_ = lean_array_get_size(v_as_4611_);
v___x_4615_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4616_ = lean_nat_dec_lt(v___x_4612_, v___x_4614_);
if (v___x_4616_ == 0)
{
lean_dec_ref(v_as_4611_);
return v___x_4613_;
}
else
{
lean_object* v___x_4617_; lean_object* v___f_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; size_t v___x_4621_; size_t v___x_4622_; lean_object* v___x_4623_; lean_object* v_snd_4624_; 
v___x_4617_ = lean_box(v___x_4616_);
v___f_4618_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4618_, 0, v___x_4617_);
v___x_4619_ = lean_box(v___x_4616_);
v___x_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
lean_ctor_set(v___x_4620_, 1, v___x_4613_);
v___x_4621_ = ((size_t)0ULL);
v___x_4622_ = lean_usize_of_nat(v___x_4614_);
v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4615_, v___f_4618_, v_as_4611_, v___x_4621_, v___x_4622_, v___x_4620_);
v_snd_4624_ = lean_ctor_get(v___x_4623_, 1);
lean_inc(v_snd_4624_);
lean_dec(v___x_4623_);
return v_snd_4624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4625_, lean_object* v_inst_4626_, lean_object* v_a_4627_, lean_object* v_p_4628_, lean_object* v_acc_4629_, lean_object* v_stx_4630_, uint8_t v_____do__lift_4631_){
_start:
{
if (v_____do__lift_4631_ == 0)
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec(v_stx_4630_);
v___x_4632_ = lean_unsigned_to_nat(2u);
v___x_4633_ = lean_nat_add(v_i_4625_, v___x_4632_);
v___x_4634_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4626_, v_a_4627_, v_p_4628_, v___x_4633_, v_acc_4629_);
return v___x_4634_;
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4635_ = lean_array_get_size(v_acc_4629_);
v___x_4636_ = lean_unsigned_to_nat(0u);
v___x_4637_ = lean_nat_dec_eq(v___x_4635_, v___x_4636_);
if (v___x_4637_ == 0)
{
uint8_t v___x_4638_; 
v___x_4638_ = lean_nat_dec_eq(v_i_4625_, v___x_4636_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; lean_object* v_sepStx_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4639_ = lean_nat_pred(v_i_4625_);
v_sepStx_4640_ = lean_array_fget_borrowed(v_a_4627_, v___x_4639_);
lean_dec(v___x_4639_);
v___x_4641_ = lean_unsigned_to_nat(2u);
v___x_4642_ = lean_nat_add(v_i_4625_, v___x_4641_);
lean_inc(v_sepStx_4640_);
v___x_4643_ = lean_array_push(v_acc_4629_, v_sepStx_4640_);
v___x_4644_ = lean_array_push(v___x_4643_, v_stx_4630_);
v___x_4645_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4626_, v_a_4627_, v_p_4628_, v___x_4642_, v___x_4644_);
return v___x_4645_;
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4646_ = lean_unsigned_to_nat(2u);
v___x_4647_ = lean_nat_add(v_i_4625_, v___x_4646_);
v___x_4648_ = lean_array_push(v_acc_4629_, v_stx_4630_);
v___x_4649_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4626_, v_a_4627_, v_p_4628_, v___x_4647_, v___x_4648_);
return v___x_4649_;
}
}
else
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4650_ = lean_unsigned_to_nat(2u);
v___x_4651_ = lean_nat_add(v_i_4625_, v___x_4650_);
v___x_4652_ = lean_array_push(v_acc_4629_, v_stx_4630_);
v___x_4653_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4626_, v_a_4627_, v_p_4628_, v___x_4651_, v___x_4652_);
return v___x_4653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4654_, lean_object* v_inst_4655_, lean_object* v_a_4656_, lean_object* v_p_4657_, lean_object* v_acc_4658_, lean_object* v_stx_4659_, lean_object* v_____do__lift_4660_){
_start:
{
uint8_t v_____do__lift_218__boxed_4661_; lean_object* v_res_4662_; 
v_____do__lift_218__boxed_4661_ = lean_unbox(v_____do__lift_4660_);
v_res_4662_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4654_, v_inst_4655_, v_a_4656_, v_p_4657_, v_acc_4658_, v_stx_4659_, v_____do__lift_218__boxed_4661_);
lean_dec(v_i_4654_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4663_, lean_object* v_a_4664_, lean_object* v_p_4665_, lean_object* v_i_4666_, lean_object* v_acc_4667_){
_start:
{
lean_object* v_toApplicative_4668_; lean_object* v_toBind_4669_; lean_object* v_toPure_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; 
v_toApplicative_4668_ = lean_ctor_get(v_inst_4663_, 0);
v_toBind_4669_ = lean_ctor_get(v_inst_4663_, 1);
lean_inc(v_toBind_4669_);
v_toPure_4670_ = lean_ctor_get(v_toApplicative_4668_, 1);
v___x_4671_ = lean_array_get_size(v_a_4664_);
v___x_4672_ = lean_nat_dec_lt(v_i_4666_, v___x_4671_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; 
lean_inc(v_toPure_4670_);
lean_dec(v_toBind_4669_);
lean_dec(v_i_4666_);
lean_dec(v_p_4665_);
lean_dec_ref(v_a_4664_);
lean_dec_ref(v_inst_4663_);
v___x_4673_ = lean_apply_2(v_toPure_4670_, lean_box(0), v_acc_4667_);
return v___x_4673_;
}
else
{
lean_object* v_stx_4674_; lean_object* v___f_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_stx_4674_ = lean_array_fget(v_a_4664_, v_i_4666_);
lean_inc(v_stx_4674_);
lean_inc(v_p_4665_);
v___f_4675_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4675_, 0, v_i_4666_);
lean_closure_set(v___f_4675_, 1, v_inst_4663_);
lean_closure_set(v___f_4675_, 2, v_a_4664_);
lean_closure_set(v___f_4675_, 3, v_p_4665_);
lean_closure_set(v___f_4675_, 4, v_acc_4667_);
lean_closure_set(v___f_4675_, 5, v_stx_4674_);
v___x_4676_ = lean_apply_1(v_p_4665_, v_stx_4674_);
v___x_4677_ = lean_apply_4(v_toBind_4669_, lean_box(0), lean_box(0), v___x_4676_, v___f_4675_);
return v___x_4677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4678_, lean_object* v_inst_4679_, lean_object* v_a_4680_, lean_object* v_p_4681_, lean_object* v_i_4682_, lean_object* v_acc_4683_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4679_, v_a_4680_, v_p_4681_, v_i_4682_, v_acc_4683_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4685_, lean_object* v_a_4686_, lean_object* v_p_4687_){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4688_ = lean_unsigned_to_nat(0u);
v___x_4689_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4690_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4685_, v_a_4686_, v_p_4687_, v___x_4688_, v___x_4689_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4691_, lean_object* v_inst_4692_, lean_object* v_a_4693_, lean_object* v_p_4694_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Array_filterSepElemsM___redArg(v_inst_4692_, v_a_4693_, v_p_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4696_, lean_object* v_x_4697_){
_start:
{
lean_object* v___x_4698_; uint8_t v___x_4699_; 
v___x_4698_ = lean_apply_1(v_p_4696_, v_x_4697_);
v___x_4699_ = lean_unbox(v___x_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4700_, lean_object* v_x_4701_){
_start:
{
uint8_t v_res_4702_; lean_object* v_r_4703_; 
v_res_4702_ = l_Array_filterSepElems___lam__0(v_p_4700_, v_x_4701_);
v_r_4703_ = lean_box(v_res_4702_);
return v_r_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4704_, lean_object* v_p_4705_, lean_object* v_i_4706_, lean_object* v_acc_4707_){
_start:
{
lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4708_ = lean_array_get_size(v_a_4704_);
v___x_4709_ = lean_nat_dec_lt(v_i_4706_, v___x_4708_);
if (v___x_4709_ == 0)
{
lean_dec(v_i_4706_);
lean_dec_ref(v_p_4705_);
return v_acc_4707_;
}
else
{
lean_object* v_stx_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; 
v_stx_4710_ = lean_array_fget_borrowed(v_a_4704_, v_i_4706_);
lean_inc_ref(v_p_4705_);
lean_inc(v_stx_4710_);
v___x_4711_ = lean_apply_1(v_p_4705_, v_stx_4710_);
v___x_4712_ = lean_unbox(v___x_4711_);
if (v___x_4712_ == 0)
{
lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = lean_unsigned_to_nat(2u);
v___x_4714_ = lean_nat_add(v_i_4706_, v___x_4713_);
lean_dec(v_i_4706_);
v_i_4706_ = v___x_4714_;
goto _start;
}
else
{
lean_object* v___x_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; 
v___x_4716_ = lean_array_get_size(v_acc_4707_);
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = lean_nat_dec_eq(v___x_4716_, v___x_4717_);
if (v___x_4718_ == 0)
{
uint8_t v___x_4719_; 
v___x_4719_ = lean_nat_dec_eq(v_i_4706_, v___x_4717_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; lean_object* v_sepStx_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4720_ = lean_nat_pred(v_i_4706_);
v_sepStx_4721_ = lean_array_fget_borrowed(v_a_4704_, v___x_4720_);
lean_dec(v___x_4720_);
v___x_4722_ = lean_unsigned_to_nat(2u);
v___x_4723_ = lean_nat_add(v_i_4706_, v___x_4722_);
lean_dec(v_i_4706_);
lean_inc(v_sepStx_4721_);
v___x_4724_ = lean_array_push(v_acc_4707_, v_sepStx_4721_);
lean_inc(v_stx_4710_);
v___x_4725_ = lean_array_push(v___x_4724_, v_stx_4710_);
v_i_4706_ = v___x_4723_;
v_acc_4707_ = v___x_4725_;
goto _start;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4727_ = lean_unsigned_to_nat(2u);
v___x_4728_ = lean_nat_add(v_i_4706_, v___x_4727_);
lean_dec(v_i_4706_);
lean_inc(v_stx_4710_);
v___x_4729_ = lean_array_push(v_acc_4707_, v_stx_4710_);
v_i_4706_ = v___x_4728_;
v_acc_4707_ = v___x_4729_;
goto _start;
}
}
else
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4731_ = lean_unsigned_to_nat(2u);
v___x_4732_ = lean_nat_add(v_i_4706_, v___x_4731_);
lean_dec(v_i_4706_);
lean_inc(v_stx_4710_);
v___x_4733_ = lean_array_push(v_acc_4707_, v_stx_4710_);
v_i_4706_ = v___x_4732_;
v_acc_4707_ = v___x_4733_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4735_, lean_object* v_p_4736_, lean_object* v_i_4737_, lean_object* v_acc_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4735_, v_p_4736_, v_i_4737_, v_acc_4738_);
lean_dec_ref(v_a_4735_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4740_, lean_object* v_p_4741_){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_unsigned_to_nat(0u);
v___x_4743_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4744_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4740_, v_p_4741_, v___x_4742_, v___x_4743_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4745_, lean_object* v_p_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4745_, v_p_4746_);
lean_dec_ref(v_a_4745_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4748_, lean_object* v_p_4749_){
_start:
{
lean_object* v___f_4750_; lean_object* v___x_4751_; 
v___f_4750_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4750_, 0, v_p_4749_);
v___x_4751_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4748_, v___f_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4752_, lean_object* v_p_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Array_filterSepElems(v_a_4752_, v_p_4753_);
lean_dec_ref(v_a_4752_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4755_, lean_object* v_acc_4756_, lean_object* v_inst_4757_, lean_object* v_a_4758_, lean_object* v_f_4759_, lean_object* v_stx_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4755_, v_acc_4756_, v_inst_4757_, v_a_4758_, v_f_4759_, v_stx_4760_);
lean_dec(v_i_4755_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4762_, lean_object* v_a_4763_, lean_object* v_f_4764_, lean_object* v_i_4765_, lean_object* v_acc_4766_){
_start:
{
lean_object* v_toApplicative_4767_; lean_object* v_toBind_4768_; lean_object* v_toPure_4769_; lean_object* v___x_4770_; uint8_t v___x_4771_; 
v_toApplicative_4767_ = lean_ctor_get(v_inst_4762_, 0);
v_toBind_4768_ = lean_ctor_get(v_inst_4762_, 1);
v_toPure_4769_ = lean_ctor_get(v_toApplicative_4767_, 1);
v___x_4770_ = lean_array_get_size(v_a_4763_);
v___x_4771_ = lean_nat_dec_lt(v_i_4765_, v___x_4770_);
if (v___x_4771_ == 0)
{
lean_object* v___x_4772_; 
lean_inc(v_toPure_4769_);
lean_dec(v_i_4765_);
lean_dec(v_f_4764_);
lean_dec_ref(v_a_4763_);
lean_dec_ref(v_inst_4762_);
v___x_4772_ = lean_apply_2(v_toPure_4769_, lean_box(0), v_acc_4766_);
return v___x_4772_;
}
else
{
lean_object* v_stx_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; uint8_t v___x_4777_; 
v_stx_4773_ = lean_array_fget_borrowed(v_a_4763_, v_i_4765_);
v___x_4774_ = lean_unsigned_to_nat(2u);
v___x_4775_ = lean_nat_mod(v_i_4765_, v___x_4774_);
v___x_4776_ = lean_unsigned_to_nat(0u);
v___x_4777_ = lean_nat_dec_eq(v___x_4775_, v___x_4776_);
lean_dec(v___x_4775_);
if (v___x_4777_ == 0)
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4778_ = lean_unsigned_to_nat(1u);
v___x_4779_ = lean_nat_add(v_i_4765_, v___x_4778_);
lean_dec(v_i_4765_);
lean_inc(v_stx_4773_);
v___x_4780_ = lean_array_push(v_acc_4766_, v_stx_4773_);
v_i_4765_ = v___x_4779_;
v_acc_4766_ = v___x_4780_;
goto _start;
}
else
{
lean_object* v___f_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
lean_inc(v_stx_4773_);
lean_inc(v_toBind_4768_);
lean_inc(v_f_4764_);
v___f_4782_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4782_, 0, v_i_4765_);
lean_closure_set(v___f_4782_, 1, v_acc_4766_);
lean_closure_set(v___f_4782_, 2, v_inst_4762_);
lean_closure_set(v___f_4782_, 3, v_a_4763_);
lean_closure_set(v___f_4782_, 4, v_f_4764_);
v___x_4783_ = lean_apply_1(v_f_4764_, v_stx_4773_);
v___x_4784_ = lean_apply_4(v_toBind_4768_, lean_box(0), lean_box(0), v___x_4783_, v___f_4782_);
return v___x_4784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4785_, lean_object* v_acc_4786_, lean_object* v_inst_4787_, lean_object* v_a_4788_, lean_object* v_f_4789_, lean_object* v_stx_4790_){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4791_ = lean_unsigned_to_nat(1u);
v___x_4792_ = lean_nat_add(v_i_4785_, v___x_4791_);
v___x_4793_ = lean_array_push(v_acc_4786_, v_stx_4790_);
v___x_4794_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4787_, v_a_4788_, v_f_4789_, v___x_4792_, v___x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4795_, lean_object* v_inst_4796_, lean_object* v_a_4797_, lean_object* v_f_4798_, lean_object* v_i_4799_, lean_object* v_acc_4800_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4796_, v_a_4797_, v_f_4798_, v_i_4799_, v_acc_4800_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4802_, lean_object* v_a_4803_, lean_object* v_f_4804_){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4805_ = lean_unsigned_to_nat(0u);
v___x_4806_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4807_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4802_, v_a_4803_, v_f_4804_, v___x_4805_, v___x_4806_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4808_, lean_object* v_inst_4809_, lean_object* v_a_4810_, lean_object* v_f_4811_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_Array_mapSepElemsM___redArg(v_inst_4809_, v_a_4810_, v_f_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4813_, lean_object* v_x_4814_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_apply_1(v_f_4813_, v_x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4816_, lean_object* v_f_4817_, lean_object* v_i_4818_, lean_object* v_acc_4819_){
_start:
{
lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4820_ = lean_array_get_size(v_a_4816_);
v___x_4821_ = lean_nat_dec_lt(v_i_4818_, v___x_4820_);
if (v___x_4821_ == 0)
{
lean_dec(v_i_4818_);
lean_dec_ref(v_f_4817_);
return v_acc_4819_;
}
else
{
lean_object* v_stx_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
v_stx_4822_ = lean_array_fget_borrowed(v_a_4816_, v_i_4818_);
v___x_4823_ = lean_unsigned_to_nat(2u);
v___x_4824_ = lean_nat_mod(v_i_4818_, v___x_4823_);
v___x_4825_ = lean_unsigned_to_nat(0u);
v___x_4826_ = lean_nat_dec_eq(v___x_4824_, v___x_4825_);
lean_dec(v___x_4824_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4828_ = lean_nat_add(v_i_4818_, v___x_4827_);
lean_dec(v_i_4818_);
lean_inc(v_stx_4822_);
v___x_4829_ = lean_array_push(v_acc_4819_, v_stx_4822_);
v_i_4818_ = v___x_4828_;
v_acc_4819_ = v___x_4829_;
goto _start;
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
lean_inc_ref(v_f_4817_);
lean_inc(v_stx_4822_);
v___x_4831_ = lean_apply_1(v_f_4817_, v_stx_4822_);
v___x_4832_ = lean_unsigned_to_nat(1u);
v___x_4833_ = lean_nat_add(v_i_4818_, v___x_4832_);
lean_dec(v_i_4818_);
v___x_4834_ = lean_array_push(v_acc_4819_, v___x_4831_);
v_i_4818_ = v___x_4833_;
v_acc_4819_ = v___x_4834_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4836_, lean_object* v_f_4837_, lean_object* v_i_4838_, lean_object* v_acc_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4836_, v_f_4837_, v_i_4838_, v_acc_4839_);
lean_dec_ref(v_a_4836_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4841_, lean_object* v_f_4842_){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4843_ = lean_unsigned_to_nat(0u);
v___x_4844_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4845_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4841_, v_f_4842_, v___x_4843_, v___x_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4846_, lean_object* v_f_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4846_, v_f_4847_);
lean_dec_ref(v_a_4846_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4849_, lean_object* v_f_4850_){
_start:
{
lean_object* v___f_4851_; lean_object* v___x_4852_; 
v___f_4851_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4851_, 0, v_f_4850_);
v___x_4852_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4849_, v___f_4851_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4853_, lean_object* v_f_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Array_mapSepElems(v_a_4853_, v_f_4854_);
lean_dec_ref(v_a_4853_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4856_, size_t v_i_4857_, size_t v_stop_4858_, lean_object* v_b_4859_){
_start:
{
lean_object* v___y_4861_; uint8_t v___x_4865_; 
v___x_4865_ = lean_usize_dec_eq(v_i_4857_, v_stop_4858_);
if (v___x_4865_ == 0)
{
lean_object* v_fst_4866_; uint8_t v___x_4867_; 
v_fst_4866_ = lean_ctor_get(v_b_4859_, 0);
v___x_4867_ = lean_unbox(v_fst_4866_);
if (v___x_4867_ == 0)
{
lean_object* v_snd_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4877_; 
v_snd_4868_ = lean_ctor_get(v_b_4859_, 1);
v_isSharedCheck_4877_ = !lean_is_exclusive(v_b_4859_);
if (v_isSharedCheck_4877_ == 0)
{
lean_object* v_unused_4878_; 
v_unused_4878_ = lean_ctor_get(v_b_4859_, 0);
lean_dec(v_unused_4878_);
v___x_4870_ = v_b_4859_;
v_isShared_4871_ = v_isSharedCheck_4877_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_snd_4868_);
lean_dec(v_b_4859_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4877_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
uint8_t v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4872_ = 1;
v___x_4873_ = lean_box(v___x_4872_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4873_);
v___x_4875_ = v___x_4870_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
lean_ctor_set(v_reuseFailAlloc_4876_, 1, v_snd_4868_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
v___y_4861_ = v___x_4875_;
goto v___jp_4860_;
}
}
}
else
{
lean_object* v_snd_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4889_; 
v_snd_4879_ = lean_ctor_get(v_b_4859_, 1);
v_isSharedCheck_4889_ = !lean_is_exclusive(v_b_4859_);
if (v_isSharedCheck_4889_ == 0)
{
lean_object* v_unused_4890_; 
v_unused_4890_ = lean_ctor_get(v_b_4859_, 0);
lean_dec(v_unused_4890_);
v___x_4881_ = v_b_4859_;
v_isShared_4882_ = v_isSharedCheck_4889_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_snd_4879_);
lean_dec(v_b_4859_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4889_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4883_ = lean_array_uget_borrowed(v_as_4856_, v_i_4857_);
lean_inc(v___x_4883_);
v___x_4884_ = lean_array_push(v_snd_4879_, v___x_4883_);
v___x_4885_ = lean_box(v___x_4865_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 1, v___x_4884_);
lean_ctor_set(v___x_4881_, 0, v___x_4885_);
v___x_4887_ = v___x_4881_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v___x_4884_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
v___y_4861_ = v___x_4887_;
goto v___jp_4860_;
}
}
}
}
else
{
return v_b_4859_;
}
v___jp_4860_:
{
size_t v___x_4862_; size_t v___x_4863_; 
v___x_4862_ = ((size_t)1ULL);
v___x_4863_ = lean_usize_add(v_i_4857_, v___x_4862_);
v_i_4857_ = v___x_4863_;
v_b_4859_ = v___y_4861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4891_, lean_object* v_i_4892_, lean_object* v_stop_4893_, lean_object* v_b_4894_){
_start:
{
size_t v_i_boxed_4895_; size_t v_stop_boxed_4896_; lean_object* v_res_4897_; 
v_i_boxed_4895_ = lean_unbox_usize(v_i_4892_);
lean_dec(v_i_4892_);
v_stop_boxed_4896_ = lean_unbox_usize(v_stop_4893_);
lean_dec(v_stop_4893_);
v_res_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4891_, v_i_boxed_4895_, v_stop_boxed_4896_, v_b_4894_);
lean_dec_ref(v_as_4891_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4898_){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
v___x_4899_ = lean_unsigned_to_nat(0u);
v___x_4900_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4901_ = lean_array_get_size(v_sa_4898_);
v___x_4902_ = lean_nat_dec_lt(v___x_4899_, v___x_4901_);
if (v___x_4902_ == 0)
{
return v___x_4900_;
}
else
{
lean_object* v___x_4903_; lean_object* v___x_4904_; size_t v___x_4905_; size_t v___x_4906_; lean_object* v___x_4907_; lean_object* v_snd_4908_; 
v___x_4903_ = lean_box(v___x_4902_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
lean_ctor_set(v___x_4904_, 1, v___x_4900_);
v___x_4905_ = ((size_t)0ULL);
v___x_4906_ = lean_usize_of_nat(v___x_4901_);
v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4898_, v___x_4905_, v___x_4906_, v___x_4904_);
v_snd_4908_ = lean_ctor_get(v___x_4907_, 1);
lean_inc(v_snd_4908_);
lean_dec_ref(v___x_4907_);
return v_snd_4908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4909_){
_start:
{
lean_object* v_res_4910_; 
v_res_4910_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4909_);
lean_dec_ref(v_sa_4909_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4911_, lean_object* v_sa_4912_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4912_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4914_, lean_object* v_sa_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_Syntax_SepArray_getElems(v_sep_4914_, v_sa_4915_);
lean_dec_ref(v_sa_4915_);
lean_dec_ref(v_sep_4914_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4917_){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4918_ = lean_unsigned_to_nat(0u);
v___x_4919_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4920_ = lean_array_get_size(v_sa_4917_);
v___x_4921_ = lean_nat_dec_lt(v___x_4918_, v___x_4920_);
if (v___x_4921_ == 0)
{
return v___x_4919_;
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4923_; size_t v___x_4924_; size_t v___x_4925_; lean_object* v___x_4926_; lean_object* v_snd_4927_; 
v___x_4922_ = lean_box(v___x_4921_);
v___x_4923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4922_);
lean_ctor_set(v___x_4923_, 1, v___x_4919_);
v___x_4924_ = ((size_t)0ULL);
v___x_4925_ = lean_usize_of_nat(v___x_4920_);
v___x_4926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4917_, v___x_4924_, v___x_4925_, v___x_4923_);
v_snd_4927_ = lean_ctor_get(v___x_4926_, 1);
lean_inc(v_snd_4927_);
lean_dec_ref(v___x_4926_);
return v_snd_4927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4928_);
lean_dec_ref(v_sa_4928_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4930_, lean_object* v_sep_4931_, lean_object* v_sa_4932_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4932_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4934_, lean_object* v_sep_4935_, lean_object* v_sa_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Syntax_TSepArray_getElems(v_k_4934_, v_sep_4935_, v_sa_4936_);
lean_dec_ref(v_sa_4936_);
lean_dec_ref(v_sep_4935_);
lean_dec(v_k_4934_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4938_, lean_object* v_sa_4939_, lean_object* v_e_4940_){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; uint8_t v___x_4943_; 
v___x_4941_ = lean_array_get_size(v_sa_4939_);
v___x_4942_ = lean_unsigned_to_nat(0u);
v___x_4943_ = lean_nat_dec_eq(v___x_4941_, v___x_4942_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4944_ = l_Lean_mkAtom(v_sep_4938_);
v___x_4945_ = lean_array_push(v_sa_4939_, v___x_4944_);
v___x_4946_ = lean_array_push(v___x_4945_, v_e_4940_);
return v___x_4946_;
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
lean_dec_ref(v_sa_4939_);
lean_dec_ref(v_sep_4938_);
v___x_4947_ = lean_unsigned_to_nat(1u);
v___x_4948_ = lean_mk_empty_array_with_capacity(v___x_4947_);
v___x_4949_ = lean_array_push(v___x_4948_, v_e_4940_);
return v___x_4949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4950_, lean_object* v_sep_4951_, lean_object* v_sa_4952_, lean_object* v_e_4953_){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4951_, v_sa_4952_, v_e_4953_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4955_, lean_object* v_sep_4956_, lean_object* v_sa_4957_, lean_object* v_e_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Lean_Syntax_TSepArray_push(v_k_4955_, v_sep_4956_, v_sa_4957_, v_e_4958_);
lean_dec(v_k_4955_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4963_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4965_){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4967_);
lean_dec_ref(v_sep_4967_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4972_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4974_, lean_object* v_k_4975_){
_start:
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4977_, lean_object* v_k_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4977_, v_k_4978_);
lean_dec_ref(v_k_4978_);
lean_dec(v_sep_4977_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4980_){
_start:
{
lean_inc_ref(v_v_4980_);
return v_v_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4981_);
lean_dec_ref(v_v_4981_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4985_; 
v___f_4985_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4988_, lean_object* v_sep_4989_){
_start:
{
lean_object* v___f_4990_; 
v___f_4990_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4991_, lean_object* v_sep_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4991_, v_sep_4992_);
lean_dec_ref(v_sep_4992_);
lean_dec(v_k_4991_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4994_, lean_object* v_sep_4995_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4996_, 0, v_k_4994_);
lean_closure_set(v___x_4996_, 1, v_sep_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4997_, lean_object* v_x_4998_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = lean_apply_1(v_inst_4997_, v_x_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___x_5002_; size_t v_sz_5003_; size_t v___x_5004_; lean_object* v___x_5005_; 
v___x_5002_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5003_ = lean_array_size(v_a_5001_);
v___x_5004_ = ((size_t)0ULL);
v___x_5005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5002_, v___f_5000_, v_sz_5003_, v___x_5004_, v_a_5001_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5006_){
_start:
{
lean_object* v___f_5007_; lean_object* v___f_5008_; 
v___f_5007_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5007_, 0, v_inst_5006_);
v___f_5008_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5008_, 0, v___f_5007_);
return v___f_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5009_, lean_object* v_k_x27_5010_, lean_object* v_inst_5011_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5011_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5013_, lean_object* v_k_x27_5014_, lean_object* v_inst_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5013_, v_k_x27_5014_, v_inst_5015_);
lean_dec(v_k_x27_5014_);
lean_dec(v_k_5013_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_5017_){
_start:
{
lean_inc_ref(v_a_5017_);
return v_a_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_5018_);
lean_dec_ref(v_a_5018_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_5022_; 
v___f_5022_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5025_){
_start:
{
lean_object* v___f_5026_; 
v___f_5026_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5027_);
lean_dec(v_k_5027_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5035_){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5036_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
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
uint32_t v_c_5065_; uint32_t v___x_5066_; uint8_t v___x_5067_; 
v_c_5065_ = lean_string_utf8_get(v_s_5062_, v_i_5063_);
v___x_5066_ = 34;
v___x_5067_ = lean_uint32_dec_eq(v_c_5065_, v___x_5066_);
if (v___x_5067_ == 0)
{
uint32_t v___x_5068_; uint8_t v___x_5069_; 
v___x_5068_ = 123;
v___x_5069_ = lean_uint32_dec_eq(v_c_5065_, v___x_5068_);
if (v___x_5069_ == 0)
{
lean_object* v_i_5070_; uint8_t v___x_5071_; 
v_i_5070_ = lean_string_utf8_next(v_s_5062_, v_i_5063_);
lean_dec(v_i_5063_);
v___x_5071_ = lean_string_utf8_at_end(v_s_5062_, v_i_5070_);
if (v___x_5071_ == 0)
{
uint32_t v___x_5072_; uint8_t v___x_5073_; 
v___x_5072_ = 92;
v___x_5073_ = lean_uint32_dec_eq(v_c_5065_, v___x_5072_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5074_; 
v___x_5074_ = lean_string_push(v_acc_5064_, v_c_5065_);
v_i_5063_ = v_i_5070_;
v_acc_5064_ = v___x_5074_;
goto _start;
}
else
{
lean_object* v___x_5076_; 
v___x_5076_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5062_, v_i_5070_);
if (lean_obj_tag(v___x_5076_) == 1)
{
lean_object* v_val_5077_; lean_object* v_fst_5078_; lean_object* v_snd_5079_; uint32_t v___x_5080_; lean_object* v___x_5081_; 
lean_dec(v_i_5070_);
v_val_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_val_5077_);
lean_dec_ref_known(v___x_5076_, 1);
v_fst_5078_ = lean_ctor_get(v_val_5077_, 0);
lean_inc(v_fst_5078_);
v_snd_5079_ = lean_ctor_get(v_val_5077_, 1);
lean_inc(v_snd_5079_);
lean_dec(v_val_5077_);
v___x_5080_ = lean_unbox_uint32(v_fst_5078_);
lean_dec(v_fst_5078_);
v___x_5081_ = lean_string_push(v_acc_5064_, v___x_5080_);
v_i_5063_ = v_snd_5079_;
v_acc_5064_ = v___x_5081_;
goto _start;
}
else
{
lean_object* v___x_5083_; 
lean_dec(v___x_5076_);
lean_inc_ref(v_s_5062_);
v___x_5083_ = l_Lean_Syntax_decodeStringGap(v_s_5062_, v_i_5070_);
lean_dec(v_i_5070_);
if (lean_obj_tag(v___x_5083_) == 1)
{
lean_object* v_val_5084_; 
v_val_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_val_5084_);
lean_dec_ref_known(v___x_5083_, 1);
v_i_5063_ = v_val_5084_;
goto _start;
}
else
{
lean_object* v___x_5086_; 
lean_dec(v___x_5083_);
lean_dec_ref(v_acc_5064_);
lean_dec_ref(v_s_5062_);
v___x_5086_ = lean_box(0);
return v___x_5086_;
}
}
}
}
else
{
lean_object* v___x_5087_; 
lean_dec(v_i_5070_);
lean_dec_ref(v_acc_5064_);
lean_dec_ref(v_s_5062_);
v___x_5087_ = lean_box(0);
return v___x_5087_;
}
}
else
{
lean_object* v___x_5088_; 
lean_dec(v_i_5063_);
lean_dec_ref(v_s_5062_);
v___x_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_acc_5064_);
return v___x_5088_;
}
}
else
{
lean_object* v___x_5089_; 
lean_dec(v_i_5063_);
lean_dec_ref(v_s_5062_);
v___x_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5089_, 0, v_acc_5064_);
return v___x_5089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5090_){
_start:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5091_ = lean_unsigned_to_nat(1u);
v___x_5092_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5093_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5090_, v___x_5091_, v___x_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5097_){
_start:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5099_ = l_Lean_Syntax_isLit_x3f(v___x_5098_, v_stx_5097_);
if (lean_obj_tag(v___x_5099_) == 0)
{
return v___x_5099_;
}
else
{
lean_object* v_val_5100_; lean_object* v___x_5101_; 
v_val_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_val_5100_);
lean_dec_ref_known(v___x_5099_, 1);
v___x_5101_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5100_);
return v___x_5101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5102_);
lean_dec(v_stx_5102_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5104_){
_start:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; 
v___x_5105_ = l_Lean_Syntax_getArgs(v_stx_5104_);
v___x_5106_ = lean_unsigned_to_nat(0u);
v___x_5107_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5108_ = lean_array_get_size(v___x_5105_);
v___x_5109_ = lean_nat_dec_lt(v___x_5106_, v___x_5108_);
if (v___x_5109_ == 0)
{
lean_dec_ref(v___x_5105_);
return v___x_5107_;
}
else
{
lean_object* v___x_5110_; lean_object* v___x_5111_; size_t v___x_5112_; size_t v___x_5113_; lean_object* v___x_5114_; lean_object* v_snd_5115_; 
v___x_5110_ = lean_box(v___x_5109_);
v___x_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5111_, 0, v___x_5110_);
lean_ctor_set(v___x_5111_, 1, v___x_5107_);
v___x_5112_ = ((size_t)0ULL);
v___x_5113_ = lean_usize_of_nat(v___x_5108_);
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5105_, v___x_5112_, v___x_5113_, v___x_5111_);
lean_dec_ref(v___x_5105_);
v_snd_5115_ = lean_ctor_get(v___x_5114_, 1);
lean_inc(v_snd_5115_);
lean_dec_ref(v___x_5114_);
return v_snd_5115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_Syntax_getSepArgs(v_stx_5116_);
lean_dec(v_stx_5116_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5118_, lean_object* v_mkElem_5119_, lean_object* v_mkLit_5120_, lean_object* v_as_5121_, size_t v_sz_5122_, size_t v_i_5123_, lean_object* v_b_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
lean_object* v_a_5128_; lean_object* v_a_5129_; lean_object* v_elem_5134_; lean_object* v___y_5135_; lean_object* v___y_5136_; uint8_t v___x_5141_; 
v___x_5141_ = lean_usize_dec_lt(v_i_5123_, v_sz_5122_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
lean_dec_ref(v_mkLit_5120_);
lean_dec_ref(v_mkElem_5119_);
lean_dec_ref(v_mkAppend_5118_);
v___x_5142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5142_, 0, v_b_5124_);
lean_ctor_set(v___x_5142_, 1, v___y_5126_);
return v___x_5142_;
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5144_; 
v_a_5143_ = lean_array_uget_borrowed(v_as_5121_, v_i_5123_);
v___x_5144_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5143_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_methods_5145_; lean_object* v_quotContext_5146_; lean_object* v_currMacroScope_5147_; lean_object* v_currRecDepth_5148_; lean_object* v_maxRecDepth_5149_; lean_object* v_ref_5150_; lean_object* v_ref_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v_methods_5145_ = lean_ctor_get(v___y_5125_, 0);
v_quotContext_5146_ = lean_ctor_get(v___y_5125_, 1);
v_currMacroScope_5147_ = lean_ctor_get(v___y_5125_, 2);
v_currRecDepth_5148_ = lean_ctor_get(v___y_5125_, 3);
v_maxRecDepth_5149_ = lean_ctor_get(v___y_5125_, 4);
v_ref_5150_ = lean_ctor_get(v___y_5125_, 5);
v_ref_5151_ = l_Lean_replaceRef(v_a_5143_, v_ref_5150_);
lean_inc(v_maxRecDepth_5149_);
lean_inc(v_currRecDepth_5148_);
lean_inc(v_currMacroScope_5147_);
lean_inc(v_quotContext_5146_);
lean_inc(v_methods_5145_);
v___x_5152_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5152_, 0, v_methods_5145_);
lean_ctor_set(v___x_5152_, 1, v_quotContext_5146_);
lean_ctor_set(v___x_5152_, 2, v_currMacroScope_5147_);
lean_ctor_set(v___x_5152_, 3, v_currRecDepth_5148_);
lean_ctor_set(v___x_5152_, 4, v_maxRecDepth_5149_);
lean_ctor_set(v___x_5152_, 5, v_ref_5151_);
lean_inc_ref(v_mkElem_5119_);
lean_inc(v_a_5143_);
v___x_5153_ = lean_apply_3(v_mkElem_5119_, v_a_5143_, v___x_5152_, v___y_5126_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v_a_5154_; lean_object* v_a_5155_; 
v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
lean_inc(v_a_5154_);
v_a_5155_ = lean_ctor_get(v___x_5153_, 1);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5153_, 2);
v_elem_5134_ = v_a_5154_;
v___y_5135_ = v___y_5125_;
v___y_5136_ = v_a_5155_;
goto v___jp_5133_;
}
else
{
lean_dec(v_b_5124_);
lean_dec_ref(v_mkLit_5120_);
lean_dec_ref(v_mkElem_5119_);
lean_dec_ref(v_mkAppend_5118_);
return v___x_5153_;
}
}
else
{
lean_object* v_val_5156_; uint8_t v___x_5157_; 
v_val_5156_ = lean_ctor_get(v___x_5144_, 0);
lean_inc_n(v_val_5156_, 2);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5157_ = lean_string_isempty(v_val_5156_);
if (v___x_5157_ == 0)
{
lean_object* v_methods_5158_; lean_object* v_quotContext_5159_; lean_object* v_currMacroScope_5160_; lean_object* v_currRecDepth_5161_; lean_object* v_maxRecDepth_5162_; lean_object* v_ref_5163_; lean_object* v_ref_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v_methods_5158_ = lean_ctor_get(v___y_5125_, 0);
v_quotContext_5159_ = lean_ctor_get(v___y_5125_, 1);
v_currMacroScope_5160_ = lean_ctor_get(v___y_5125_, 2);
v_currRecDepth_5161_ = lean_ctor_get(v___y_5125_, 3);
v_maxRecDepth_5162_ = lean_ctor_get(v___y_5125_, 4);
v_ref_5163_ = lean_ctor_get(v___y_5125_, 5);
v_ref_5164_ = l_Lean_replaceRef(v_a_5143_, v_ref_5163_);
lean_inc(v_maxRecDepth_5162_);
lean_inc(v_currRecDepth_5161_);
lean_inc(v_currMacroScope_5160_);
lean_inc(v_quotContext_5159_);
lean_inc(v_methods_5158_);
v___x_5165_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5165_, 0, v_methods_5158_);
lean_ctor_set(v___x_5165_, 1, v_quotContext_5159_);
lean_ctor_set(v___x_5165_, 2, v_currMacroScope_5160_);
lean_ctor_set(v___x_5165_, 3, v_currRecDepth_5161_);
lean_ctor_set(v___x_5165_, 4, v_maxRecDepth_5162_);
lean_ctor_set(v___x_5165_, 5, v_ref_5164_);
lean_inc_ref(v_mkLit_5120_);
v___x_5166_ = lean_apply_3(v_mkLit_5120_, v_val_5156_, v___x_5165_, v___y_5126_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v_a_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
v_a_5168_ = lean_ctor_get(v___x_5166_, 1);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5166_, 2);
v_elem_5134_ = v_a_5167_;
v___y_5135_ = v___y_5125_;
v___y_5136_ = v_a_5168_;
goto v___jp_5133_;
}
else
{
lean_dec(v_b_5124_);
lean_dec_ref(v_mkLit_5120_);
lean_dec_ref(v_mkElem_5119_);
lean_dec_ref(v_mkAppend_5118_);
return v___x_5166_;
}
}
else
{
lean_dec(v_val_5156_);
v_a_5128_ = v_b_5124_;
v_a_5129_ = v___y_5126_;
goto v___jp_5127_;
}
}
}
v___jp_5127_:
{
size_t v___x_5130_; size_t v___x_5131_; 
v___x_5130_ = ((size_t)1ULL);
v___x_5131_ = lean_usize_add(v_i_5123_, v___x_5130_);
v_i_5123_ = v___x_5131_;
v_b_5124_ = v_a_5128_;
v___y_5126_ = v_a_5129_;
goto _start;
}
v___jp_5133_:
{
uint8_t v___x_5137_; 
v___x_5137_ = l_Lean_Syntax_isMissing(v_b_5124_);
if (v___x_5137_ == 0)
{
lean_object* v___x_5138_; 
lean_inc_ref(v_mkAppend_5118_);
lean_inc_ref(v___y_5135_);
v___x_5138_ = lean_apply_4(v_mkAppend_5118_, v_b_5124_, v_elem_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v_a_5140_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
v_a_5140_ = lean_ctor_get(v___x_5138_, 1);
lean_inc(v_a_5140_);
lean_dec_ref_known(v___x_5138_, 2);
v_a_5128_ = v_a_5139_;
v_a_5129_ = v_a_5140_;
goto v___jp_5127_;
}
else
{
lean_dec_ref(v_mkLit_5120_);
lean_dec_ref(v_mkElem_5119_);
lean_dec_ref(v_mkAppend_5118_);
return v___x_5138_;
}
}
else
{
lean_dec(v_b_5124_);
v_a_5128_ = v_elem_5134_;
v_a_5129_ = v___y_5136_;
goto v___jp_5127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5169_, lean_object* v_mkElem_5170_, lean_object* v_mkLit_5171_, lean_object* v_as_5172_, lean_object* v_sz_5173_, lean_object* v_i_5174_, lean_object* v_b_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
size_t v_sz_boxed_5178_; size_t v_i_boxed_5179_; lean_object* v_res_5180_; 
v_sz_boxed_5178_ = lean_unbox_usize(v_sz_5173_);
lean_dec(v_sz_5173_);
v_i_boxed_5179_ = lean_unbox_usize(v_i_5174_);
lean_dec(v_i_5174_);
v_res_5180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5169_, v_mkElem_5170_, v_mkLit_5171_, v_as_5172_, v_sz_boxed_5178_, v_i_boxed_5179_, v_b_5175_, v___y_5176_, v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v_as_5172_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5181_, lean_object* v_mkAppend_5182_, lean_object* v_mkElem_5183_, lean_object* v_mkLit_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_result_5187_; size_t v_sz_5188_; size_t v___x_5189_; lean_object* v___x_5190_; 
v_result_5187_ = lean_box(0);
v_sz_5188_ = lean_array_size(v_chunks_5181_);
v___x_5189_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5184_);
v___x_5190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5182_, v_mkElem_5183_, v_mkLit_5184_, v_chunks_5181_, v_sz_5188_, v___x_5189_, v_result_5187_, v_a_5185_, v_a_5186_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v_a_5192_; uint8_t v___x_5193_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
v_a_5192_ = lean_ctor_get(v___x_5190_, 1);
v___x_5193_ = l_Lean_Syntax_isMissing(v_a_5191_);
if (v___x_5193_ == 0)
{
lean_dec_ref(v_mkLit_5184_);
return v___x_5190_;
}
else
{
lean_object* v___x_5194_; lean_object* v___x_5195_; 
lean_inc(v_a_5192_);
lean_dec_ref_known(v___x_5190_, 2);
v___x_5194_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5185_);
v___x_5195_ = lean_apply_3(v_mkLit_5184_, v___x_5194_, v_a_5185_, v_a_5192_);
return v___x_5195_;
}
}
else
{
lean_dec_ref(v_mkLit_5184_);
return v___x_5190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5196_, lean_object* v_mkAppend_5197_, lean_object* v_mkElem_5198_, lean_object* v_mkLit_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5196_, v_mkAppend_5197_, v_mkElem_5198_, v_mkLit_5199_, v_a_5200_, v_a_5201_);
lean_dec_ref(v_a_5200_);
lean_dec_ref(v_chunks_5196_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5207_, lean_object* v_b_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v_ref_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v_ref_5211_ = lean_ctor_get(v___y_5209_, 5);
v___x_5212_ = 0;
v___x_5213_ = l_Lean_SourceInfo_fromRef(v_ref_5211_, v___x_5212_);
v___x_5214_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5215_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5213_);
v___x_5216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5213_);
lean_ctor_set(v___x_5216_, 1, v___x_5215_);
v___x_5217_ = l_Lean_Syntax_node3(v___x_5213_, v___x_5214_, v_a_5207_, v___x_5216_, v_b_5208_);
v___x_5218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5218_, 0, v___x_5217_);
lean_ctor_set(v___x_5218_, 1, v___y_5210_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5219_, lean_object* v_b_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5219_, v_b_5220_, v___y_5221_, v___y_5222_);
lean_dec_ref(v___y_5221_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5224_, lean_object* v_a_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v_ref_5228_; uint8_t v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v_ref_5228_ = lean_ctor_get(v___y_5226_, 5);
v___x_5229_ = 0;
v___x_5230_ = l_Lean_SourceInfo_fromRef(v_ref_5228_, v___x_5229_);
v___x_5231_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5232_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5230_);
v___x_5233_ = l_Lean_Syntax_node1(v___x_5230_, v___x_5232_, v_a_5225_);
v___x_5234_ = l_Lean_Syntax_node2(v___x_5230_, v___x_5231_, v_ofInterpFn_5224_, v___x_5233_);
v___x_5235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5234_);
lean_ctor_set(v___x_5235_, 1, v___y_5227_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5236_, lean_object* v_a_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5236_, v_a_5237_, v___y_5238_, v___y_5239_);
lean_dec_ref(v___y_5238_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5241_, lean_object* v_s_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_ref_5245_; uint8_t v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; 
v_ref_5245_ = lean_ctor_get(v___y_5243_, 5);
v___x_5246_ = 0;
v___x_5247_ = l_Lean_SourceInfo_fromRef(v_ref_5245_, v___x_5246_);
v___x_5248_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5249_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5250_ = lean_box(2);
v___x_5251_ = l_Lean_Syntax_mkStrLit(v_s_5242_, v___x_5250_);
lean_inc(v___x_5247_);
v___x_5252_ = l_Lean_Syntax_node1(v___x_5247_, v___x_5249_, v___x_5251_);
v___x_5253_ = l_Lean_Syntax_node2(v___x_5247_, v___x_5248_, v_ofLitFn_5241_, v___x_5252_);
v___x_5254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5253_);
lean_ctor_set(v___x_5254_, 1, v___y_5244_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5255_, lean_object* v_s_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5255_, v_s_5256_, v___y_5257_, v___y_5258_);
lean_dec_ref(v___y_5257_);
return v_res_5259_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5277_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5278_ = l_String_toRawSubstring_x27(v___x_5277_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5299_, lean_object* v_type_5300_, lean_object* v_ofInterpFn_5301_, lean_object* v_ofLitFn_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_){
_start:
{
lean_object* v___f_5305_; lean_object* v___f_5306_; lean_object* v___f_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___f_5305_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5306_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5306_, 0, v_ofInterpFn_5301_);
v___f_5307_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5307_, 0, v_ofLitFn_5302_);
v___x_5308_ = l_Lean_Syntax_getArgs(v_interpStr_5299_);
v___x_5309_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5308_, v___f_5305_, v___f_5306_, v___f_5307_, v_a_5303_, v_a_5304_);
lean_dec_ref(v___x_5308_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5342_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
v_a_5311_ = lean_ctor_get(v___x_5309_, 1);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5313_ = v___x_5309_;
v_isShared_5314_ = v_isSharedCheck_5342_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_inc(v_a_5310_);
lean_dec(v___x_5309_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5342_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v_quotContext_5315_; lean_object* v_currMacroScope_5316_; lean_object* v_ref_5317_; uint8_t v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5340_; 
v_quotContext_5315_ = lean_ctor_get(v_a_5303_, 1);
v_currMacroScope_5316_ = lean_ctor_get(v_a_5303_, 2);
v_ref_5317_ = lean_ctor_get(v_a_5303_, 5);
v___x_5318_ = 0;
v___x_5319_ = l_Lean_SourceInfo_fromRef(v_ref_5317_, v___x_5318_);
v___x_5320_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5321_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5322_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5319_, 7);
v___x_5323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5319_);
lean_ctor_set(v___x_5323_, 1, v___x_5322_);
v___x_5324_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5325_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5326_ = lean_box(0);
lean_inc(v_currMacroScope_5316_);
lean_inc(v_quotContext_5315_);
v___x_5327_ = l_Lean_addMacroScope(v_quotContext_5315_, v___x_5326_, v_currMacroScope_5316_);
v___x_5328_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5319_);
lean_ctor_set(v___x_5329_, 1, v___x_5325_);
lean_ctor_set(v___x_5329_, 2, v___x_5327_);
lean_ctor_set(v___x_5329_, 3, v___x_5328_);
v___x_5330_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5324_, v___x_5329_);
v___x_5331_ = l_Lean_Syntax_node2(v___x_5319_, v___x_5321_, v___x_5323_, v___x_5330_);
v___x_5332_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5319_);
lean_ctor_set(v___x_5333_, 1, v___x_5332_);
v___x_5334_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5335_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5334_, v_type_5300_);
v___x_5336_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5319_);
lean_ctor_set(v___x_5337_, 1, v___x_5336_);
v___x_5338_ = l_Lean_Syntax_node5(v___x_5319_, v___x_5320_, v___x_5331_, v_a_5310_, v___x_5333_, v___x_5335_, v___x_5337_);
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v___x_5338_);
v___x_5340_ = v___x_5313_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5338_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v_a_5311_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
else
{
lean_object* v_a_5343_; lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec(v_type_5300_);
v_a_5343_ = lean_ctor_get(v___x_5309_, 0);
v_a_5344_ = lean_ctor_get(v___x_5309_, 1);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5309_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_inc(v_a_5343_);
lean_dec(v___x_5309_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5343_);
lean_ctor_set(v_reuseFailAlloc_5350_, 1, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5352_, lean_object* v_type_5353_, lean_object* v_ofInterpFn_5354_, lean_object* v_ofLitFn_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5352_, v_type_5353_, v_ofInterpFn_5354_, v_ofLitFn_5355_, v_a_5356_, v_a_5357_);
lean_dec_ref(v_a_5356_);
lean_dec(v_interpStr_5352_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5359_){
_start:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; 
v___x_5360_ = lean_unsigned_to_nat(1u);
v___x_5361_ = l_Lean_Syntax_getArg(v_stx_5359_, v___x_5360_);
if (lean_obj_tag(v___x_5361_) == 1)
{
lean_object* v_kind_5362_; 
v_kind_5362_ = lean_ctor_get(v___x_5361_, 1);
lean_inc(v_kind_5362_);
if (lean_obj_tag(v_kind_5362_) == 1)
{
lean_object* v_pre_5363_; 
v_pre_5363_ = lean_ctor_get(v_kind_5362_, 0);
lean_inc(v_pre_5363_);
if (lean_obj_tag(v_pre_5363_) == 1)
{
lean_object* v_pre_5364_; 
v_pre_5364_ = lean_ctor_get(v_pre_5363_, 0);
lean_inc(v_pre_5364_);
if (lean_obj_tag(v_pre_5364_) == 1)
{
lean_object* v_pre_5365_; 
v_pre_5365_ = lean_ctor_get(v_pre_5364_, 0);
lean_inc(v_pre_5365_);
if (lean_obj_tag(v_pre_5365_) == 1)
{
lean_object* v_pre_5366_; 
v_pre_5366_ = lean_ctor_get(v_pre_5365_, 0);
if (lean_obj_tag(v_pre_5366_) == 0)
{
lean_object* v_args_5367_; lean_object* v_str_5368_; lean_object* v_str_5369_; lean_object* v_str_5370_; lean_object* v_str_5371_; lean_object* v___x_5372_; uint8_t v___x_5373_; 
v_args_5367_ = lean_ctor_get(v___x_5361_, 2);
lean_inc_ref(v_args_5367_);
lean_dec_ref_known(v___x_5361_, 3);
v_str_5368_ = lean_ctor_get(v_kind_5362_, 1);
lean_inc_ref(v_str_5368_);
lean_dec_ref_known(v_kind_5362_, 2);
v_str_5369_ = lean_ctor_get(v_pre_5363_, 1);
lean_inc_ref(v_str_5369_);
lean_dec_ref_known(v_pre_5363_, 2);
v_str_5370_ = lean_ctor_get(v_pre_5364_, 1);
lean_inc_ref(v_str_5370_);
lean_dec_ref_known(v_pre_5364_, 2);
v_str_5371_ = lean_ctor_get(v_pre_5365_, 1);
lean_inc_ref(v_str_5371_);
lean_dec_ref_known(v_pre_5365_, 2);
v___x_5372_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5373_ = lean_string_dec_eq(v_str_5371_, v___x_5372_);
lean_dec_ref(v_str_5371_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
lean_dec_ref(v_str_5370_);
lean_dec_ref(v_str_5369_);
lean_dec_ref(v_str_5368_);
lean_dec_ref(v_args_5367_);
v___x_5374_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5374_;
}
else
{
lean_object* v___x_5375_; uint8_t v___x_5376_; 
v___x_5375_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5376_ = lean_string_dec_eq(v_str_5370_, v___x_5375_);
lean_dec_ref(v_str_5370_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; 
lean_dec_ref(v_str_5369_);
lean_dec_ref(v_str_5368_);
lean_dec_ref(v_args_5367_);
v___x_5377_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5377_;
}
else
{
lean_object* v___x_5378_; uint8_t v___x_5379_; 
v___x_5378_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5379_ = lean_string_dec_eq(v_str_5369_, v___x_5378_);
lean_dec_ref(v_str_5369_);
if (v___x_5379_ == 0)
{
lean_object* v___x_5380_; 
lean_dec_ref(v_str_5368_);
lean_dec_ref(v_args_5367_);
v___x_5380_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5380_;
}
else
{
lean_object* v___x_5381_; uint8_t v___x_5382_; 
v___x_5381_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5382_ = lean_string_dec_eq(v_str_5368_, v___x_5381_);
lean_dec_ref(v_str_5368_);
if (v___x_5382_ == 0)
{
lean_object* v___x_5383_; 
lean_dec_ref(v_args_5367_);
v___x_5383_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5383_;
}
else
{
lean_object* v___x_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5384_ = lean_array_get_size(v_args_5367_);
v___x_5385_ = lean_unsigned_to_nat(2u);
v___x_5386_ = lean_nat_dec_eq(v___x_5384_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; 
lean_dec_ref(v_args_5367_);
v___x_5387_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5387_;
}
else
{
lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5388_ = lean_unsigned_to_nat(0u);
v___x_5389_ = lean_array_fget(v_args_5367_, v___x_5388_);
lean_dec_ref(v_args_5367_);
if (lean_obj_tag(v___x_5389_) == 2)
{
lean_object* v_val_5390_; 
v_val_5390_ = lean_ctor_get(v___x_5389_, 1);
lean_inc_ref(v_val_5390_);
lean_dec_ref_known(v___x_5389_, 2);
return v_val_5390_;
}
else
{
lean_object* v___x_5391_; 
lean_dec(v___x_5389_);
v___x_5391_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5391_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5392_; 
lean_dec_ref_known(v_pre_5365_, 2);
lean_dec_ref_known(v_pre_5364_, 2);
lean_dec_ref_known(v_pre_5363_, 2);
lean_dec_ref_known(v_kind_5362_, 2);
lean_dec_ref_known(v___x_5361_, 3);
v___x_5392_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5392_;
}
}
else
{
lean_object* v___x_5393_; 
lean_dec(v_pre_5365_);
lean_dec_ref_known(v_pre_5364_, 2);
lean_dec_ref_known(v_pre_5363_, 2);
lean_dec_ref_known(v_kind_5362_, 2);
lean_dec_ref_known(v___x_5361_, 3);
v___x_5393_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5393_;
}
}
else
{
lean_object* v___x_5394_; 
lean_dec(v_pre_5364_);
lean_dec_ref_known(v_pre_5363_, 2);
lean_dec_ref_known(v_kind_5362_, 2);
lean_dec_ref_known(v___x_5361_, 3);
v___x_5394_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5394_;
}
}
else
{
lean_object* v___x_5395_; 
lean_dec(v_pre_5363_);
lean_dec_ref_known(v_kind_5362_, 2);
lean_dec_ref_known(v___x_5361_, 3);
v___x_5395_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5395_;
}
}
else
{
lean_object* v___x_5396_; 
lean_dec_ref_known(v___x_5361_, 3);
lean_dec(v_kind_5362_);
v___x_5396_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5396_;
}
}
else
{
lean_object* v___x_5397_; 
lean_dec(v___x_5361_);
v___x_5397_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l_Lean_TSyntax_getDocString(v_stx_5398_);
lean_dec(v_stx_5398_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5418_, lean_object* v_prec_5419_){
_start:
{
lean_object* v___y_5421_; lean_object* v___y_5428_; lean_object* v___y_5435_; lean_object* v___y_5442_; lean_object* v___y_5449_; lean_object* v___y_5456_; 
switch(v_x_5418_)
{
case 0:
{
lean_object* v___x_5462_; uint8_t v___x_5463_; 
v___x_5462_ = lean_unsigned_to_nat(1024u);
v___x_5463_ = lean_nat_dec_le(v___x_5462_, v_prec_5419_);
if (v___x_5463_ == 0)
{
lean_object* v___x_5464_; 
v___x_5464_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5421_ = v___x_5464_;
goto v___jp_5420_;
}
else
{
lean_object* v___x_5465_; 
v___x_5465_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5421_ = v___x_5465_;
goto v___jp_5420_;
}
}
case 1:
{
lean_object* v___x_5466_; uint8_t v___x_5467_; 
v___x_5466_ = lean_unsigned_to_nat(1024u);
v___x_5467_ = lean_nat_dec_le(v___x_5466_, v_prec_5419_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; 
v___x_5468_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5428_ = v___x_5468_;
goto v___jp_5427_;
}
else
{
lean_object* v___x_5469_; 
v___x_5469_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5428_ = v___x_5469_;
goto v___jp_5427_;
}
}
case 2:
{
lean_object* v___x_5470_; uint8_t v___x_5471_; 
v___x_5470_ = lean_unsigned_to_nat(1024u);
v___x_5471_ = lean_nat_dec_le(v___x_5470_, v_prec_5419_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5472_; 
v___x_5472_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5435_ = v___x_5472_;
goto v___jp_5434_;
}
else
{
lean_object* v___x_5473_; 
v___x_5473_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5435_ = v___x_5473_;
goto v___jp_5434_;
}
}
case 3:
{
lean_object* v___x_5474_; uint8_t v___x_5475_; 
v___x_5474_ = lean_unsigned_to_nat(1024u);
v___x_5475_ = lean_nat_dec_le(v___x_5474_, v_prec_5419_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5476_; 
v___x_5476_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5442_ = v___x_5476_;
goto v___jp_5441_;
}
else
{
lean_object* v___x_5477_; 
v___x_5477_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5442_ = v___x_5477_;
goto v___jp_5441_;
}
}
case 4:
{
lean_object* v___x_5478_; uint8_t v___x_5479_; 
v___x_5478_ = lean_unsigned_to_nat(1024u);
v___x_5479_ = lean_nat_dec_le(v___x_5478_, v_prec_5419_);
if (v___x_5479_ == 0)
{
lean_object* v___x_5480_; 
v___x_5480_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5449_ = v___x_5480_;
goto v___jp_5448_;
}
else
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5449_ = v___x_5481_;
goto v___jp_5448_;
}
}
default: 
{
lean_object* v___x_5482_; uint8_t v___x_5483_; 
v___x_5482_ = lean_unsigned_to_nat(1024u);
v___x_5483_ = lean_nat_dec_le(v___x_5482_, v_prec_5419_);
if (v___x_5483_ == 0)
{
lean_object* v___x_5484_; 
v___x_5484_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5456_ = v___x_5484_;
goto v___jp_5455_;
}
else
{
lean_object* v___x_5485_; 
v___x_5485_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5456_ = v___x_5485_;
goto v___jp_5455_;
}
}
}
v___jp_5420_:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5422_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5421_);
v___x_5423_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5423_, 0, v___y_5421_);
lean_ctor_set(v___x_5423_, 1, v___x_5422_);
v___x_5424_ = 0;
v___x_5425_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5425_, 0, v___x_5423_);
lean_ctor_set_uint8(v___x_5425_, sizeof(void*)*1, v___x_5424_);
v___x_5426_ = l_Repr_addAppParen(v___x_5425_, v_prec_5419_);
return v___x_5426_;
}
v___jp_5427_:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; uint8_t v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5429_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5428_);
v___x_5430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___y_5428_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = 0;
v___x_5432_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5432_, 0, v___x_5430_);
lean_ctor_set_uint8(v___x_5432_, sizeof(void*)*1, v___x_5431_);
v___x_5433_ = l_Repr_addAppParen(v___x_5432_, v_prec_5419_);
return v___x_5433_;
}
v___jp_5434_:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; uint8_t v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v___x_5436_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5435_);
v___x_5437_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5437_, 0, v___y_5435_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
v___x_5438_ = 0;
v___x_5439_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5439_, 0, v___x_5437_);
lean_ctor_set_uint8(v___x_5439_, sizeof(void*)*1, v___x_5438_);
v___x_5440_ = l_Repr_addAppParen(v___x_5439_, v_prec_5419_);
return v___x_5440_;
}
v___jp_5441_:
{
lean_object* v___x_5443_; lean_object* v___x_5444_; uint8_t v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5443_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5442_);
v___x_5444_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5444_, 0, v___y_5442_);
lean_ctor_set(v___x_5444_, 1, v___x_5443_);
v___x_5445_ = 0;
v___x_5446_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5446_, 0, v___x_5444_);
lean_ctor_set_uint8(v___x_5446_, sizeof(void*)*1, v___x_5445_);
v___x_5447_ = l_Repr_addAppParen(v___x_5446_, v_prec_5419_);
return v___x_5447_;
}
v___jp_5448_:
{
lean_object* v___x_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5450_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5449_);
v___x_5451_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5451_, 0, v___y_5449_);
lean_ctor_set(v___x_5451_, 1, v___x_5450_);
v___x_5452_ = 0;
v___x_5453_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5453_, 0, v___x_5451_);
lean_ctor_set_uint8(v___x_5453_, sizeof(void*)*1, v___x_5452_);
v___x_5454_ = l_Repr_addAppParen(v___x_5453_, v_prec_5419_);
return v___x_5454_;
}
v___jp_5455_:
{
lean_object* v___x_5457_; lean_object* v___x_5458_; uint8_t v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5457_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5456_);
v___x_5458_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5458_, 0, v___y_5456_);
lean_ctor_set(v___x_5458_, 1, v___x_5457_);
v___x_5459_ = 0;
v___x_5460_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5460_, 0, v___x_5458_);
lean_ctor_set_uint8(v___x_5460_, sizeof(void*)*1, v___x_5459_);
v___x_5461_ = l_Repr_addAppParen(v___x_5460_, v_prec_5419_);
return v___x_5461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5486_, lean_object* v_prec_5487_){
_start:
{
uint8_t v_x_329__boxed_5488_; lean_object* v_res_5489_; 
v_x_329__boxed_5488_ = lean_unbox(v_x_5486_);
v_res_5489_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5488_, v_prec_5487_);
lean_dec(v_prec_5487_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5501_, lean_object* v_prec_5502_){
_start:
{
lean_object* v___y_5504_; lean_object* v___y_5511_; lean_object* v___y_5518_; 
switch(v_x_5501_)
{
case 0:
{
lean_object* v___x_5524_; uint8_t v___x_5525_; 
v___x_5524_ = lean_unsigned_to_nat(1024u);
v___x_5525_ = lean_nat_dec_le(v___x_5524_, v_prec_5502_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5526_; 
v___x_5526_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5504_ = v___x_5526_;
goto v___jp_5503_;
}
else
{
lean_object* v___x_5527_; 
v___x_5527_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5504_ = v___x_5527_;
goto v___jp_5503_;
}
}
case 1:
{
lean_object* v___x_5528_; uint8_t v___x_5529_; 
v___x_5528_ = lean_unsigned_to_nat(1024u);
v___x_5529_ = lean_nat_dec_le(v___x_5528_, v_prec_5502_);
if (v___x_5529_ == 0)
{
lean_object* v___x_5530_; 
v___x_5530_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5511_ = v___x_5530_;
goto v___jp_5510_;
}
else
{
lean_object* v___x_5531_; 
v___x_5531_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5511_ = v___x_5531_;
goto v___jp_5510_;
}
}
default: 
{
lean_object* v___x_5532_; uint8_t v___x_5533_; 
v___x_5532_ = lean_unsigned_to_nat(1024u);
v___x_5533_ = lean_nat_dec_le(v___x_5532_, v_prec_5502_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
v___x_5534_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5518_ = v___x_5534_;
goto v___jp_5517_;
}
else
{
lean_object* v___x_5535_; 
v___x_5535_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5518_ = v___x_5535_;
goto v___jp_5517_;
}
}
}
v___jp_5503_:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; uint8_t v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5505_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5504_);
v___x_5506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5506_, 0, v___y_5504_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
v___x_5507_ = 0;
v___x_5508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5508_, 0, v___x_5506_);
lean_ctor_set_uint8(v___x_5508_, sizeof(void*)*1, v___x_5507_);
v___x_5509_ = l_Repr_addAppParen(v___x_5508_, v_prec_5502_);
return v___x_5509_;
}
v___jp_5510_:
{
lean_object* v___x_5512_; lean_object* v___x_5513_; uint8_t v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5512_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5511_);
v___x_5513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5513_, 0, v___y_5511_);
lean_ctor_set(v___x_5513_, 1, v___x_5512_);
v___x_5514_ = 0;
v___x_5515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5515_, 0, v___x_5513_);
lean_ctor_set_uint8(v___x_5515_, sizeof(void*)*1, v___x_5514_);
v___x_5516_ = l_Repr_addAppParen(v___x_5515_, v_prec_5502_);
return v___x_5516_;
}
v___jp_5517_:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; uint8_t v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5519_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5518_);
v___x_5520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5520_, 0, v___y_5518_);
lean_ctor_set(v___x_5520_, 1, v___x_5519_);
v___x_5521_ = 0;
v___x_5522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5522_, 0, v___x_5520_);
lean_ctor_set_uint8(v___x_5522_, sizeof(void*)*1, v___x_5521_);
v___x_5523_ = l_Repr_addAppParen(v___x_5522_, v_prec_5502_);
return v___x_5523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5536_, lean_object* v_prec_5537_){
_start:
{
uint8_t v_x_167__boxed_5538_; lean_object* v_res_5539_; 
v_x_167__boxed_5538_ = lean_unbox(v_x_5536_);
v_res_5539_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5538_, v_prec_5537_);
lean_dec(v_prec_5537_);
return v_res_5539_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; 
v___x_5551_ = lean_unsigned_to_nat(8u);
v___x_5552_ = lean_nat_to_int(v___x_5551_);
return v___x_5552_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5562_ = lean_unsigned_to_nat(13u);
v___x_5563_ = lean_nat_to_int(v___x_5562_);
return v___x_5563_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5573_ = lean_unsigned_to_nat(10u);
v___x_5574_ = lean_nat_to_int(v___x_5573_);
return v___x_5574_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = lean_unsigned_to_nat(14u);
v___x_5579_ = lean_nat_to_int(v___x_5578_);
return v___x_5579_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; 
v___x_5583_ = lean_unsigned_to_nat(19u);
v___x_5584_ = lean_nat_to_int(v___x_5583_);
return v___x_5584_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_unsigned_to_nat(20u);
v___x_5589_ = lean_nat_to_int(v___x_5588_);
return v___x_5589_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; 
v___x_5596_ = lean_unsigned_to_nat(9u);
v___x_5597_ = lean_nat_to_int(v___x_5596_);
return v___x_5597_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5604_ = lean_unsigned_to_nat(12u);
v___x_5605_ = lean_nat_to_int(v___x_5604_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5612_){
_start:
{
uint8_t v_zeta_5613_; uint8_t v_beta_5614_; uint8_t v_eta_5615_; uint8_t v_etaStruct_5616_; uint8_t v_iota_5617_; uint8_t v_proj_5618_; uint8_t v_decide_5619_; uint8_t v_autoUnfold_5620_; uint8_t v_failIfUnchanged_5621_; uint8_t v_unfoldPartialApp_5622_; uint8_t v_zetaDelta_5623_; uint8_t v_index_5624_; uint8_t v_zetaUnused_5625_; uint8_t v_zetaHave_5626_; uint8_t v_locals_5627_; uint8_t v_instances_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; uint8_t v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; 
v_zeta_5613_ = lean_ctor_get_uint8(v_x_5612_, 0);
v_beta_5614_ = lean_ctor_get_uint8(v_x_5612_, 1);
v_eta_5615_ = lean_ctor_get_uint8(v_x_5612_, 2);
v_etaStruct_5616_ = lean_ctor_get_uint8(v_x_5612_, 3);
v_iota_5617_ = lean_ctor_get_uint8(v_x_5612_, 4);
v_proj_5618_ = lean_ctor_get_uint8(v_x_5612_, 5);
v_decide_5619_ = lean_ctor_get_uint8(v_x_5612_, 6);
v_autoUnfold_5620_ = lean_ctor_get_uint8(v_x_5612_, 7);
v_failIfUnchanged_5621_ = lean_ctor_get_uint8(v_x_5612_, 8);
v_unfoldPartialApp_5622_ = lean_ctor_get_uint8(v_x_5612_, 9);
v_zetaDelta_5623_ = lean_ctor_get_uint8(v_x_5612_, 10);
v_index_5624_ = lean_ctor_get_uint8(v_x_5612_, 11);
v_zetaUnused_5625_ = lean_ctor_get_uint8(v_x_5612_, 12);
v_zetaHave_5626_ = lean_ctor_get_uint8(v_x_5612_, 13);
v_locals_5627_ = lean_ctor_get_uint8(v_x_5612_, 14);
v_instances_5628_ = lean_ctor_get_uint8(v_x_5612_, 15);
v___x_5629_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5630_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5631_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5632_ = lean_unsigned_to_nat(0u);
v___x_5633_ = l_Bool_repr___redArg(v_zeta_5613_);
v___x_5634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5631_);
lean_ctor_set(v___x_5634_, 1, v___x_5633_);
v___x_5635_ = 0;
v___x_5636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set_uint8(v___x_5636_, sizeof(void*)*1, v___x_5635_);
v___x_5637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5630_);
lean_ctor_set(v___x_5637_, 1, v___x_5636_);
v___x_5638_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5637_);
lean_ctor_set(v___x_5639_, 1, v___x_5638_);
v___x_5640_ = lean_box(1);
v___x_5641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5639_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5641_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5643_);
lean_ctor_set(v___x_5644_, 1, v___x_5629_);
v___x_5645_ = l_Bool_repr___redArg(v_beta_5614_);
v___x_5646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5631_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
v___x_5647_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set_uint8(v___x_5647_, sizeof(void*)*1, v___x_5635_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5644_);
lean_ctor_set(v___x_5648_, 1, v___x_5647_);
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5648_);
lean_ctor_set(v___x_5649_, 1, v___x_5638_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set(v___x_5650_, 1, v___x_5640_);
v___x_5651_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5650_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5629_);
v___x_5654_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5655_ = l_Bool_repr___redArg(v_eta_5615_);
v___x_5656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set_uint8(v___x_5657_, sizeof(void*)*1, v___x_5635_);
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5653_);
lean_ctor_set(v___x_5658_, 1, v___x_5657_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set(v___x_5659_, 1, v___x_5638_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set(v___x_5660_, 1, v___x_5640_);
v___x_5661_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5660_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___x_5629_);
v___x_5664_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5665_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5616_, v___x_5632_);
v___x_5666_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*1, v___x_5635_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5663_);
lean_ctor_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set(v___x_5669_, 1, v___x_5638_);
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5669_);
lean_ctor_set(v___x_5670_, 1, v___x_5640_);
v___x_5671_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5670_);
lean_ctor_set(v___x_5672_, 1, v___x_5671_);
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
lean_ctor_set(v___x_5673_, 1, v___x_5629_);
v___x_5674_ = l_Bool_repr___redArg(v_iota_5617_);
v___x_5675_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5631_);
lean_ctor_set(v___x_5675_, 1, v___x_5674_);
v___x_5676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
lean_ctor_set_uint8(v___x_5676_, sizeof(void*)*1, v___x_5635_);
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5673_);
lean_ctor_set(v___x_5677_, 1, v___x_5676_);
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set(v___x_5678_, 1, v___x_5638_);
v___x_5679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set(v___x_5679_, 1, v___x_5640_);
v___x_5680_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5679_);
lean_ctor_set(v___x_5681_, 1, v___x_5680_);
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set(v___x_5682_, 1, v___x_5629_);
v___x_5683_ = l_Bool_repr___redArg(v_proj_5618_);
v___x_5684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5631_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set_uint8(v___x_5685_, sizeof(void*)*1, v___x_5635_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5682_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5686_);
lean_ctor_set(v___x_5687_, 1, v___x_5638_);
v___x_5688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set(v___x_5688_, 1, v___x_5640_);
v___x_5689_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5688_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5629_);
v___x_5692_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5693_ = l_Bool_repr___redArg(v_decide_5619_);
v___x_5694_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set_uint8(v___x_5695_, sizeof(void*)*1, v___x_5635_);
v___x_5696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5691_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
lean_ctor_set(v___x_5697_, 1, v___x_5638_);
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5697_);
lean_ctor_set(v___x_5698_, 1, v___x_5640_);
v___x_5699_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5698_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
lean_ctor_set(v___x_5701_, 1, v___x_5629_);
v___x_5702_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5703_ = l_Bool_repr___redArg(v_autoUnfold_5620_);
v___x_5704_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5702_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set_uint8(v___x_5705_, sizeof(void*)*1, v___x_5635_);
v___x_5706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5701_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
v___x_5707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
lean_ctor_set(v___x_5707_, 1, v___x_5638_);
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5707_);
lean_ctor_set(v___x_5708_, 1, v___x_5640_);
v___x_5709_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5708_);
lean_ctor_set(v___x_5710_, 1, v___x_5709_);
v___x_5711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set(v___x_5711_, 1, v___x_5629_);
v___x_5712_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5713_ = l_Bool_repr___redArg(v_failIfUnchanged_5621_);
v___x_5714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5712_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set_uint8(v___x_5715_, sizeof(void*)*1, v___x_5635_);
v___x_5716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5711_);
lean_ctor_set(v___x_5716_, 1, v___x_5715_);
v___x_5717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
lean_ctor_set(v___x_5717_, 1, v___x_5638_);
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set(v___x_5718_, 1, v___x_5640_);
v___x_5719_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5718_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set(v___x_5721_, 1, v___x_5629_);
v___x_5722_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5723_ = l_Bool_repr___redArg(v_unfoldPartialApp_5622_);
v___x_5724_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5722_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
lean_ctor_set_uint8(v___x_5725_, sizeof(void*)*1, v___x_5635_);
v___x_5726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5721_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5726_);
lean_ctor_set(v___x_5727_, 1, v___x_5638_);
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
lean_ctor_set(v___x_5728_, 1, v___x_5640_);
v___x_5729_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5728_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
lean_ctor_set(v___x_5731_, 1, v___x_5629_);
v___x_5732_ = l_Bool_repr___redArg(v_zetaDelta_5623_);
v___x_5733_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5664_);
lean_ctor_set(v___x_5733_, 1, v___x_5732_);
v___x_5734_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5734_, 0, v___x_5733_);
lean_ctor_set_uint8(v___x_5734_, sizeof(void*)*1, v___x_5635_);
v___x_5735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5731_);
lean_ctor_set(v___x_5735_, 1, v___x_5734_);
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
lean_ctor_set(v___x_5736_, 1, v___x_5638_);
v___x_5737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v___x_5640_);
v___x_5738_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5737_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5739_);
lean_ctor_set(v___x_5740_, 1, v___x_5629_);
v___x_5741_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5742_ = l_Bool_repr___redArg(v_index_5624_);
v___x_5743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5741_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set_uint8(v___x_5744_, sizeof(void*)*1, v___x_5635_);
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5740_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5745_);
lean_ctor_set(v___x_5746_, 1, v___x_5638_);
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5746_);
lean_ctor_set(v___x_5747_, 1, v___x_5640_);
v___x_5748_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set(v___x_5750_, 1, v___x_5629_);
v___x_5751_ = l_Bool_repr___redArg(v_zetaUnused_5625_);
v___x_5752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5702_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___x_5753_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
lean_ctor_set_uint8(v___x_5753_, sizeof(void*)*1, v___x_5635_);
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5750_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v___x_5755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5754_);
lean_ctor_set(v___x_5755_, 1, v___x_5638_);
v___x_5756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
lean_ctor_set(v___x_5756_, 1, v___x_5640_);
v___x_5757_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5756_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5758_);
lean_ctor_set(v___x_5759_, 1, v___x_5629_);
v___x_5760_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5761_ = l_Bool_repr___redArg(v_zetaHave_5626_);
v___x_5762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5760_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5763_, 0, v___x_5762_);
lean_ctor_set_uint8(v___x_5763_, sizeof(void*)*1, v___x_5635_);
v___x_5764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5759_);
lean_ctor_set(v___x_5764_, 1, v___x_5763_);
v___x_5765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5764_);
lean_ctor_set(v___x_5765_, 1, v___x_5638_);
v___x_5766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5765_);
lean_ctor_set(v___x_5766_, 1, v___x_5640_);
v___x_5767_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___x_5766_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5769_, 0, v___x_5768_);
lean_ctor_set(v___x_5769_, 1, v___x_5629_);
v___x_5770_ = l_Bool_repr___redArg(v_locals_5627_);
v___x_5771_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5771_, 0, v___x_5692_);
lean_ctor_set(v___x_5771_, 1, v___x_5770_);
v___x_5772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5772_, 0, v___x_5771_);
lean_ctor_set_uint8(v___x_5772_, sizeof(void*)*1, v___x_5635_);
v___x_5773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5773_, 0, v___x_5769_);
lean_ctor_set(v___x_5773_, 1, v___x_5772_);
v___x_5774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5773_);
lean_ctor_set(v___x_5774_, 1, v___x_5638_);
v___x_5775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5775_, 0, v___x_5774_);
lean_ctor_set(v___x_5775_, 1, v___x_5640_);
v___x_5776_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5775_);
lean_ctor_set(v___x_5777_, 1, v___x_5776_);
v___x_5778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5778_, 0, v___x_5777_);
lean_ctor_set(v___x_5778_, 1, v___x_5629_);
v___x_5779_ = l_Bool_repr___redArg(v_instances_5628_);
v___x_5780_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5780_, 0, v___x_5664_);
lean_ctor_set(v___x_5780_, 1, v___x_5779_);
v___x_5781_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5781_, 0, v___x_5780_);
lean_ctor_set_uint8(v___x_5781_, sizeof(void*)*1, v___x_5635_);
v___x_5782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5778_);
lean_ctor_set(v___x_5782_, 1, v___x_5781_);
v___x_5783_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5784_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5785_, 0, v___x_5784_);
lean_ctor_set(v___x_5785_, 1, v___x_5782_);
v___x_5786_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5785_);
lean_ctor_set(v___x_5787_, 1, v___x_5786_);
v___x_5788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5788_, 0, v___x_5783_);
lean_ctor_set(v___x_5788_, 1, v___x_5787_);
v___x_5789_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5789_, 0, v___x_5788_);
lean_ctor_set_uint8(v___x_5789_, sizeof(void*)*1, v___x_5635_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5790_);
lean_dec_ref(v_x_5790_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5792_, lean_object* v_prec_5793_){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5792_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5795_, lean_object* v_prec_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Lean_Meta_instReprConfig_repr(v_x_5795_, v_prec_5796_);
lean_dec(v_prec_5796_);
lean_dec_ref(v_x_5795_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5805_, lean_object* v_x_5806_){
_start:
{
if (lean_obj_tag(v_x_5805_) == 0)
{
lean_object* v___x_5807_; 
v___x_5807_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5807_;
}
else
{
lean_object* v_val_5808_; lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_5819_; 
v_val_5808_ = lean_ctor_get(v_x_5805_, 0);
v_isSharedCheck_5819_ = !lean_is_exclusive(v_x_5805_);
if (v_isSharedCheck_5819_ == 0)
{
v___x_5810_ = v_x_5805_;
v_isShared_5811_ = v_isSharedCheck_5819_;
goto v_resetjp_5809_;
}
else
{
lean_inc(v_val_5808_);
lean_dec(v_x_5805_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_5819_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5815_; 
v___x_5812_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5813_ = l_Nat_reprFast(v_val_5808_);
if (v_isShared_5811_ == 0)
{
lean_ctor_set_tag(v___x_5810_, 3);
lean_ctor_set(v___x_5810_, 0, v___x_5813_);
v___x_5815_ = v___x_5810_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5816_, 0, v___x_5812_);
lean_ctor_set(v___x_5816_, 1, v___x_5815_);
v___x_5817_ = l_Repr_addAppParen(v___x_5816_, v_x_5806_);
return v___x_5817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5820_, lean_object* v_x_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5820_, v_x_5821_);
lean_dec(v_x_5821_);
return v_res_5822_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5835_ = lean_unsigned_to_nat(21u);
v___x_5836_ = lean_nat_to_int(v___x_5835_);
return v___x_5836_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5843_ = lean_unsigned_to_nat(11u);
v___x_5844_ = lean_nat_to_int(v___x_5843_);
return v___x_5844_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5860_ = lean_unsigned_to_nat(23u);
v___x_5861_ = lean_nat_to_int(v___x_5860_);
return v___x_5861_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_unsigned_to_nat(16u);
v___x_5866_ = lean_nat_to_int(v___x_5865_);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5873_ = lean_unsigned_to_nat(15u);
v___x_5874_ = lean_nat_to_int(v___x_5873_);
return v___x_5874_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5881_ = lean_unsigned_to_nat(17u);
v___x_5882_ = lean_nat_to_int(v___x_5881_);
return v___x_5882_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5889_ = lean_unsigned_to_nat(18u);
v___x_5890_ = lean_nat_to_int(v___x_5889_);
return v___x_5890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5891_){
_start:
{
lean_object* v_maxSteps_5892_; lean_object* v_maxDischargeDepth_5893_; uint8_t v_contextual_5894_; uint8_t v_memoize_5895_; uint8_t v_singlePass_5896_; uint8_t v_zeta_5897_; uint8_t v_beta_5898_; uint8_t v_eta_5899_; uint8_t v_etaStruct_5900_; uint8_t v_iota_5901_; uint8_t v_proj_5902_; uint8_t v_decide_5903_; uint8_t v_arith_5904_; uint8_t v_autoUnfold_5905_; uint8_t v_dsimp_5906_; uint8_t v_failIfUnchanged_5907_; uint8_t v_ground_5908_; uint8_t v_unfoldPartialApp_5909_; uint8_t v_zetaDelta_5910_; uint8_t v_index_5911_; uint8_t v_implicitDefEqProofs_5912_; uint8_t v_zetaUnused_5913_; uint8_t v_catchRuntime_5914_; uint8_t v_zetaHave_5915_; uint8_t v_letToHave_5916_; uint8_t v_congrConsts_5917_; uint8_t v_bitVecOfNat_5918_; uint8_t v_warnExponents_5919_; uint8_t v_suggestions_5920_; lean_object* v_maxSuggestions_5921_; uint8_t v_locals_5922_; uint8_t v_instances_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; uint8_t v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; 
v_maxSteps_5892_ = lean_ctor_get(v_x_5891_, 0);
lean_inc(v_maxSteps_5892_);
v_maxDischargeDepth_5893_ = lean_ctor_get(v_x_5891_, 1);
lean_inc(v_maxDischargeDepth_5893_);
v_contextual_5894_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3);
v_memoize_5895_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 1);
v_singlePass_5896_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 2);
v_zeta_5897_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 3);
v_beta_5898_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 4);
v_eta_5899_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 5);
v_etaStruct_5900_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 6);
v_iota_5901_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 7);
v_proj_5902_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 8);
v_decide_5903_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 9);
v_arith_5904_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 10);
v_autoUnfold_5905_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 11);
v_dsimp_5906_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5907_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 13);
v_ground_5908_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5909_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 15);
v_zetaDelta_5910_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 16);
v_index_5911_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5912_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 18);
v_zetaUnused_5913_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 19);
v_catchRuntime_5914_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 20);
v_zetaHave_5915_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 21);
v_letToHave_5916_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 22);
v_congrConsts_5917_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5918_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 24);
v_warnExponents_5919_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 25);
v_suggestions_5920_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 26);
v_maxSuggestions_5921_ = lean_ctor_get(v_x_5891_, 2);
lean_inc(v_maxSuggestions_5921_);
v_locals_5922_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 27);
v_instances_5923_ = lean_ctor_get_uint8(v_x_5891_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5891_);
v___x_5924_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5925_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5926_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5927_ = l_Nat_reprFast(v_maxSteps_5892_);
v___x_5928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
v___x_5929_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5926_);
lean_ctor_set(v___x_5929_, 1, v___x_5928_);
v___x_5930_ = 0;
v___x_5931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5931_, 0, v___x_5929_);
lean_ctor_set_uint8(v___x_5931_, sizeof(void*)*1, v___x_5930_);
v___x_5932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5925_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_box(1);
v___x_5936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set(v___x_5939_, 1, v___x_5924_);
v___x_5940_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5941_ = l_Nat_reprFast(v_maxDischargeDepth_5893_);
v___x_5942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5941_);
v___x_5943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5940_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
v___x_5944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
lean_ctor_set_uint8(v___x_5944_, sizeof(void*)*1, v___x_5930_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5939_);
lean_ctor_set(v___x_5945_, 1, v___x_5944_);
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
lean_ctor_set(v___x_5946_, 1, v___x_5933_);
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set(v___x_5947_, 1, v___x_5935_);
v___x_5948_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5947_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set(v___x_5950_, 1, v___x_5924_);
v___x_5951_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5952_ = lean_unsigned_to_nat(0u);
v___x_5953_ = l_Bool_repr___redArg(v_contextual_5894_);
v___x_5954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5951_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
v___x_5955_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set_uint8(v___x_5955_, sizeof(void*)*1, v___x_5930_);
v___x_5956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5950_);
lean_ctor_set(v___x_5956_, 1, v___x_5955_);
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
lean_ctor_set(v___x_5957_, 1, v___x_5933_);
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5935_);
v___x_5959_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5958_);
lean_ctor_set(v___x_5960_, 1, v___x_5959_);
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set(v___x_5961_, 1, v___x_5924_);
v___x_5962_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5963_ = l_Bool_repr___redArg(v_memoize_5895_);
v___x_5964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5962_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set_uint8(v___x_5965_, sizeof(void*)*1, v___x_5930_);
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5961_);
lean_ctor_set(v___x_5966_, 1, v___x_5965_);
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5966_);
lean_ctor_set(v___x_5967_, 1, v___x_5933_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5967_);
lean_ctor_set(v___x_5968_, 1, v___x_5935_);
v___x_5969_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5968_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
lean_ctor_set(v___x_5971_, 1, v___x_5924_);
v___x_5972_ = l_Bool_repr___redArg(v_singlePass_5896_);
v___x_5973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5951_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5974_, 0, v___x_5973_);
lean_ctor_set_uint8(v___x_5974_, sizeof(void*)*1, v___x_5930_);
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5971_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set(v___x_5976_, 1, v___x_5933_);
v___x_5977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
lean_ctor_set(v___x_5977_, 1, v___x_5935_);
v___x_5978_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5977_);
lean_ctor_set(v___x_5979_, 1, v___x_5978_);
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set(v___x_5980_, 1, v___x_5924_);
v___x_5981_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5982_ = l_Bool_repr___redArg(v_zeta_5897_);
v___x_5983_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5981_);
lean_ctor_set(v___x_5983_, 1, v___x_5982_);
v___x_5984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set_uint8(v___x_5984_, sizeof(void*)*1, v___x_5930_);
v___x_5985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5980_);
lean_ctor_set(v___x_5985_, 1, v___x_5984_);
v___x_5986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5985_);
lean_ctor_set(v___x_5986_, 1, v___x_5933_);
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5935_);
v___x_5988_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5987_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
lean_ctor_set(v___x_5990_, 1, v___x_5924_);
v___x_5991_ = l_Bool_repr___redArg(v_beta_5898_);
v___x_5992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5981_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
v___x_5993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set_uint8(v___x_5993_, sizeof(void*)*1, v___x_5930_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5990_);
lean_ctor_set(v___x_5994_, 1, v___x_5993_);
v___x_5995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5994_);
lean_ctor_set(v___x_5995_, 1, v___x_5933_);
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v___x_5935_);
v___x_5997_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5996_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
lean_ctor_set(v___x_5999_, 1, v___x_5924_);
v___x_6000_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_6001_ = l_Bool_repr___redArg(v_eta_5899_);
v___x_6002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6000_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set_uint8(v___x_6003_, sizeof(void*)*1, v___x_5930_);
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_5999_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set(v___x_6005_, 1, v___x_5933_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___x_5935_);
v___x_6007_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6006_);
lean_ctor_set(v___x_6008_, 1, v___x_6007_);
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6008_);
lean_ctor_set(v___x_6009_, 1, v___x_5924_);
v___x_6010_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_6011_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5900_, v___x_5952_);
v___x_6012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6010_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set_uint8(v___x_6013_, sizeof(void*)*1, v___x_5930_);
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6009_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set(v___x_6015_, 1, v___x_5933_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5935_);
v___x_6017_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_6018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6016_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
lean_ctor_set(v___x_6019_, 1, v___x_5924_);
v___x_6020_ = l_Bool_repr___redArg(v_iota_5901_);
v___x_6021_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_5981_);
lean_ctor_set(v___x_6021_, 1, v___x_6020_);
v___x_6022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
lean_ctor_set_uint8(v___x_6022_, sizeof(void*)*1, v___x_5930_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6019_);
lean_ctor_set(v___x_6023_, 1, v___x_6022_);
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set(v___x_6024_, 1, v___x_5933_);
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set(v___x_6025_, 1, v___x_5935_);
v___x_6026_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6025_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set(v___x_6028_, 1, v___x_5924_);
v___x_6029_ = l_Bool_repr___redArg(v_proj_5902_);
v___x_6030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_5981_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set_uint8(v___x_6031_, sizeof(void*)*1, v___x_5930_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6028_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set(v___x_6033_, 1, v___x_5933_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set(v___x_6034_, 1, v___x_5935_);
v___x_6035_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6034_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
lean_ctor_set(v___x_6037_, 1, v___x_5924_);
v___x_6038_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6039_ = l_Bool_repr___redArg(v_decide_5903_);
v___x_6040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6038_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set_uint8(v___x_6041_, sizeof(void*)*1, v___x_5930_);
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6037_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set(v___x_6043_, 1, v___x_5933_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_5935_);
v___x_6045_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6044_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6046_);
lean_ctor_set(v___x_6047_, 1, v___x_5924_);
v___x_6048_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6049_ = l_Bool_repr___redArg(v_arith_5904_);
v___x_6050_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6048_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set_uint8(v___x_6051_, sizeof(void*)*1, v___x_5930_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6047_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set(v___x_6053_, 1, v___x_5933_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5935_);
v___x_6055_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6054_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set(v___x_6057_, 1, v___x_5924_);
v___x_6058_ = l_Bool_repr___redArg(v_autoUnfold_5905_);
v___x_6059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_5951_);
lean_ctor_set(v___x_6059_, 1, v___x_6058_);
v___x_6060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
lean_ctor_set_uint8(v___x_6060_, sizeof(void*)*1, v___x_5930_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6057_);
lean_ctor_set(v___x_6061_, 1, v___x_6060_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
lean_ctor_set(v___x_6062_, 1, v___x_5933_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5935_);
v___x_6064_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6063_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
lean_ctor_set(v___x_6066_, 1, v___x_5924_);
v___x_6067_ = l_Bool_repr___redArg(v_dsimp_5906_);
v___x_6068_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6048_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set_uint8(v___x_6069_, sizeof(void*)*1, v___x_5930_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6066_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
lean_ctor_set(v___x_6071_, 1, v___x_5933_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_5935_);
v___x_6073_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6072_);
lean_ctor_set(v___x_6074_, 1, v___x_6073_);
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set(v___x_6075_, 1, v___x_5924_);
v___x_6076_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6077_ = l_Bool_repr___redArg(v_failIfUnchanged_5907_);
v___x_6078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6076_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set_uint8(v___x_6079_, sizeof(void*)*1, v___x_5930_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6075_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6080_);
lean_ctor_set(v___x_6081_, 1, v___x_5933_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5935_);
v___x_6083_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6082_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5924_);
v___x_6086_ = l_Bool_repr___redArg(v_ground_5908_);
v___x_6087_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6038_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set_uint8(v___x_6088_, sizeof(void*)*1, v___x_5930_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6085_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set(v___x_6090_, 1, v___x_5933_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_5935_);
v___x_6092_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6091_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set(v___x_6094_, 1, v___x_5924_);
v___x_6095_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6096_ = l_Bool_repr___redArg(v_unfoldPartialApp_5909_);
v___x_6097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6095_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set_uint8(v___x_6098_, sizeof(void*)*1, v___x_5930_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6094_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_5933_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5935_);
v___x_6102_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_5924_);
v___x_6105_ = l_Bool_repr___redArg(v_zetaDelta_5910_);
v___x_6106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6010_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
v___x_6107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set_uint8(v___x_6107_, sizeof(void*)*1, v___x_5930_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6104_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set(v___x_6109_, 1, v___x_5933_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_5935_);
v___x_6111_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6110_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_5924_);
v___x_6114_ = l_Bool_repr___redArg(v_index_5911_);
v___x_6115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6048_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
v___x_6116_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set_uint8(v___x_6116_, sizeof(void*)*1, v___x_5930_);
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6113_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set(v___x_6118_, 1, v___x_5933_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_5935_);
v___x_6120_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6119_);
lean_ctor_set(v___x_6121_, 1, v___x_6120_);
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set(v___x_6122_, 1, v___x_5924_);
v___x_6123_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6124_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5912_);
v___x_6125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6123_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set_uint8(v___x_6126_, sizeof(void*)*1, v___x_5930_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6122_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
lean_ctor_set(v___x_6128_, 1, v___x_5933_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_5935_);
v___x_6130_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6129_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5924_);
v___x_6133_ = l_Bool_repr___redArg(v_zetaUnused_5913_);
v___x_6134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_5951_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set_uint8(v___x_6135_, sizeof(void*)*1, v___x_5930_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6132_);
lean_ctor_set(v___x_6136_, 1, v___x_6135_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set(v___x_6137_, 1, v___x_5933_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_5935_);
v___x_6139_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6140_);
lean_ctor_set(v___x_6141_, 1, v___x_5924_);
v___x_6142_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6143_ = l_Bool_repr___redArg(v_catchRuntime_5914_);
v___x_6144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6142_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*1, v___x_5930_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6141_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set(v___x_6147_, 1, v___x_5933_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_5935_);
v___x_6149_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_5924_);
v___x_6152_ = l_Bool_repr___redArg(v_zetaHave_5915_);
v___x_6153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_5926_);
lean_ctor_set(v___x_6153_, 1, v___x_6152_);
v___x_6154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6154_, 0, v___x_6153_);
lean_ctor_set_uint8(v___x_6154_, sizeof(void*)*1, v___x_5930_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6151_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
lean_ctor_set(v___x_6156_, 1, v___x_5933_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set(v___x_6157_, 1, v___x_5935_);
v___x_6158_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6157_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set(v___x_6160_, 1, v___x_5924_);
v___x_6161_ = l_Bool_repr___redArg(v_letToHave_5916_);
v___x_6162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6010_);
lean_ctor_set(v___x_6162_, 1, v___x_6161_);
v___x_6163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6163_, 0, v___x_6162_);
lean_ctor_set_uint8(v___x_6163_, sizeof(void*)*1, v___x_5930_);
v___x_6164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6160_);
lean_ctor_set(v___x_6164_, 1, v___x_6163_);
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6164_);
lean_ctor_set(v___x_6165_, 1, v___x_5933_);
v___x_6166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set(v___x_6166_, 1, v___x_5935_);
v___x_6167_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6166_);
lean_ctor_set(v___x_6168_, 1, v___x_6167_);
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
lean_ctor_set(v___x_6169_, 1, v___x_5924_);
v___x_6170_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6171_ = l_Bool_repr___redArg(v_congrConsts_5917_);
v___x_6172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6170_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set_uint8(v___x_6173_, sizeof(void*)*1, v___x_5930_);
v___x_6174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6169_);
lean_ctor_set(v___x_6174_, 1, v___x_6173_);
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
lean_ctor_set(v___x_6175_, 1, v___x_5933_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set(v___x_6176_, 1, v___x_5935_);
v___x_6177_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6176_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_5924_);
v___x_6180_ = l_Bool_repr___redArg(v_bitVecOfNat_5918_);
v___x_6181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6170_);
lean_ctor_set(v___x_6181_, 1, v___x_6180_);
v___x_6182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6182_, 0, v___x_6181_);
lean_ctor_set_uint8(v___x_6182_, sizeof(void*)*1, v___x_5930_);
v___x_6183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6179_);
lean_ctor_set(v___x_6183_, 1, v___x_6182_);
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6183_);
lean_ctor_set(v___x_6184_, 1, v___x_5933_);
v___x_6185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___x_5935_);
v___x_6186_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6185_);
lean_ctor_set(v___x_6187_, 1, v___x_6186_);
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
lean_ctor_set(v___x_6188_, 1, v___x_5924_);
v___x_6189_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6190_ = l_Bool_repr___redArg(v_warnExponents_5919_);
v___x_6191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6189_);
lean_ctor_set(v___x_6191_, 1, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set_uint8(v___x_6192_, sizeof(void*)*1, v___x_5930_);
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6188_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6193_);
lean_ctor_set(v___x_6194_, 1, v___x_5933_);
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6194_);
lean_ctor_set(v___x_6195_, 1, v___x_5935_);
v___x_6196_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6195_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___x_5924_);
v___x_6199_ = l_Bool_repr___redArg(v_suggestions_5920_);
v___x_6200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6170_);
lean_ctor_set(v___x_6200_, 1, v___x_6199_);
v___x_6201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6201_, 0, v___x_6200_);
lean_ctor_set_uint8(v___x_6201_, sizeof(void*)*1, v___x_5930_);
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6198_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
v___x_6203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set(v___x_6203_, 1, v___x_5933_);
v___x_6204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6203_);
lean_ctor_set(v___x_6204_, 1, v___x_5935_);
v___x_6205_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6204_);
lean_ctor_set(v___x_6206_, 1, v___x_6205_);
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
lean_ctor_set(v___x_6207_, 1, v___x_5924_);
v___x_6208_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6209_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5921_, v___x_5952_);
v___x_6210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6208_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
lean_ctor_set_uint8(v___x_6211_, sizeof(void*)*1, v___x_5930_);
v___x_6212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6207_);
lean_ctor_set(v___x_6212_, 1, v___x_6211_);
v___x_6213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6212_);
lean_ctor_set(v___x_6213_, 1, v___x_5933_);
v___x_6214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6213_);
lean_ctor_set(v___x_6214_, 1, v___x_5935_);
v___x_6215_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6214_);
lean_ctor_set(v___x_6216_, 1, v___x_6215_);
v___x_6217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
lean_ctor_set(v___x_6217_, 1, v___x_5924_);
v___x_6218_ = l_Bool_repr___redArg(v_locals_5922_);
v___x_6219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6038_);
lean_ctor_set(v___x_6219_, 1, v___x_6218_);
v___x_6220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6220_, 0, v___x_6219_);
lean_ctor_set_uint8(v___x_6220_, sizeof(void*)*1, v___x_5930_);
v___x_6221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6217_);
lean_ctor_set(v___x_6221_, 1, v___x_6220_);
v___x_6222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6222_, 0, v___x_6221_);
lean_ctor_set(v___x_6222_, 1, v___x_5933_);
v___x_6223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6222_);
lean_ctor_set(v___x_6223_, 1, v___x_5935_);
v___x_6224_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6223_);
lean_ctor_set(v___x_6225_, 1, v___x_6224_);
v___x_6226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6225_);
lean_ctor_set(v___x_6226_, 1, v___x_5924_);
v___x_6227_ = l_Bool_repr___redArg(v_instances_5923_);
v___x_6228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6228_, 0, v___x_6010_);
lean_ctor_set(v___x_6228_, 1, v___x_6227_);
v___x_6229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6229_, 0, v___x_6228_);
lean_ctor_set_uint8(v___x_6229_, sizeof(void*)*1, v___x_5930_);
v___x_6230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6230_, 0, v___x_6226_);
lean_ctor_set(v___x_6230_, 1, v___x_6229_);
v___x_6231_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6232_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6233_, 0, v___x_6232_);
lean_ctor_set(v___x_6233_, 1, v___x_6230_);
v___x_6234_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6235_, 0, v___x_6233_);
lean_ctor_set(v___x_6235_, 1, v___x_6234_);
v___x_6236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6236_, 0, v___x_6231_);
lean_ctor_set(v___x_6236_, 1, v___x_6235_);
v___x_6237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6237_, 0, v___x_6236_);
lean_ctor_set_uint8(v___x_6237_, sizeof(void*)*1, v___x_5930_);
return v___x_6237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6238_, lean_object* v_prec_6239_){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6238_);
return v___x_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6241_, lean_object* v_prec_6242_){
_start:
{
lean_object* v_res_6243_; 
v_res_6243_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6241_, v_prec_6242_);
lean_dec(v_prec_6242_);
return v_res_6243_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6246_, lean_object* v_x_6247_){
_start:
{
if (lean_obj_tag(v_x_6247_) == 0)
{
uint8_t v___x_6248_; 
v___x_6248_ = 0;
return v___x_6248_;
}
else
{
lean_object* v_head_6249_; lean_object* v_tail_6250_; uint8_t v___x_6251_; 
v_head_6249_ = lean_ctor_get(v_x_6247_, 0);
v_tail_6250_ = lean_ctor_get(v_x_6247_, 1);
v___x_6251_ = lean_nat_dec_eq(v_a_6246_, v_head_6249_);
if (v___x_6251_ == 0)
{
v_x_6247_ = v_tail_6250_;
goto _start;
}
else
{
return v___x_6251_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6253_, lean_object* v_x_6254_){
_start:
{
uint8_t v_res_6255_; lean_object* v_r_6256_; 
v_res_6255_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6253_, v_x_6254_);
lean_dec(v_x_6254_);
lean_dec(v_a_6253_);
v_r_6256_ = lean_box(v_res_6255_);
return v_r_6256_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6257_, lean_object* v_x_6258_){
_start:
{
switch(lean_obj_tag(v_x_6257_))
{
case 0:
{
uint8_t v___x_6259_; 
v___x_6259_ = 1;
return v___x_6259_;
}
case 1:
{
lean_object* v_idxs_6260_; uint8_t v___x_6261_; 
v_idxs_6260_ = lean_ctor_get(v_x_6257_, 0);
v___x_6261_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6258_, v_idxs_6260_);
return v___x_6261_;
}
default: 
{
lean_object* v_idxs_6262_; uint8_t v___x_6263_; 
v_idxs_6262_ = lean_ctor_get(v_x_6257_, 0);
v___x_6263_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6258_, v_idxs_6262_);
if (v___x_6263_ == 0)
{
uint8_t v___x_6264_; 
v___x_6264_ = 1;
return v___x_6264_;
}
else
{
uint8_t v___x_6265_; 
v___x_6265_ = 0;
return v___x_6265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6266_, lean_object* v_x_6267_){
_start:
{
uint8_t v_res_6268_; lean_object* v_r_6269_; 
v_res_6268_ = l_Lean_Meta_Occurrences_contains(v_x_6266_, v_x_6267_);
lean_dec(v_x_6267_);
lean_dec(v_x_6266_);
v_r_6269_ = lean_box(v_res_6268_);
return v_r_6269_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6270_){
_start:
{
if (lean_obj_tag(v_x_6270_) == 0)
{
uint8_t v___x_6271_; 
v___x_6271_ = 1;
return v___x_6271_;
}
else
{
uint8_t v___x_6272_; 
v___x_6272_ = 0;
return v___x_6272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6273_){
_start:
{
uint8_t v_res_6274_; lean_object* v_r_6275_; 
v_res_6274_ = l_Lean_Meta_Occurrences_isAll(v_x_6273_);
lean_dec(v_x_6273_);
v_r_6275_ = lean_box(v_res_6274_);
return v_r_6275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(uint8_t v_x_6276_){
_start:
{
lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6277_ = lean_box(v_x_6276_);
v___x_6278_ = lean_obj_tag_nat(v___x_6277_);
lean_dec(v___x_6277_);
return v___x_6278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl___boxed(lean_object* v_x_6279_){
_start:
{
uint8_t v_x_4__boxed_6280_; lean_object* v_res_6281_; 
v_x_4__boxed_6280_ = lean_unbox(v_x_6279_);
v_res_6281_ = l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(v_x_4__boxed_6280_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6282_){
_start:
{
lean_inc(v_k_6282_);
return v_k_6282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6283_){
_start:
{
lean_object* v_res_6284_; 
v_res_6284_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6283_);
lean_dec(v_k_6283_);
return v_res_6284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6285_, lean_object* v_ctorIdx_6286_, uint8_t v_t_6287_, lean_object* v_h_6288_, lean_object* v_k_6289_){
_start:
{
lean_inc(v_k_6289_);
return v_k_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6290_, lean_object* v_ctorIdx_6291_, lean_object* v_t_6292_, lean_object* v_h_6293_, lean_object* v_k_6294_){
_start:
{
uint8_t v_t_boxed_6295_; lean_object* v_res_6296_; 
v_t_boxed_6295_ = lean_unbox(v_t_6292_);
v_res_6296_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6290_, v_ctorIdx_6291_, v_t_boxed_6295_, v_h_6293_, v_k_6294_);
lean_dec(v_k_6294_);
lean_dec(v_ctorIdx_6291_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6297_){
_start:
{
lean_inc(v_nonDependentFirst_6297_);
return v_nonDependentFirst_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6298_){
_start:
{
lean_object* v_res_6299_; 
v_res_6299_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6298_);
lean_dec(v_nonDependentFirst_6298_);
return v_res_6299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6300_, uint8_t v_t_6301_, lean_object* v_h_6302_, lean_object* v_nonDependentFirst_6303_){
_start:
{
lean_inc(v_nonDependentFirst_6303_);
return v_nonDependentFirst_6303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6304_, lean_object* v_t_6305_, lean_object* v_h_6306_, lean_object* v_nonDependentFirst_6307_){
_start:
{
uint8_t v_t_boxed_6308_; lean_object* v_res_6309_; 
v_t_boxed_6308_ = lean_unbox(v_t_6305_);
v_res_6309_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6304_, v_t_boxed_6308_, v_h_6306_, v_nonDependentFirst_6307_);
lean_dec(v_nonDependentFirst_6307_);
return v_res_6309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6310_){
_start:
{
lean_inc(v_nonDependentOnly_6310_);
return v_nonDependentOnly_6310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6311_){
_start:
{
lean_object* v_res_6312_; 
v_res_6312_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6311_);
lean_dec(v_nonDependentOnly_6311_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6313_, uint8_t v_t_6314_, lean_object* v_h_6315_, lean_object* v_nonDependentOnly_6316_){
_start:
{
lean_inc(v_nonDependentOnly_6316_);
return v_nonDependentOnly_6316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6317_, lean_object* v_t_6318_, lean_object* v_h_6319_, lean_object* v_nonDependentOnly_6320_){
_start:
{
uint8_t v_t_boxed_6321_; lean_object* v_res_6322_; 
v_t_boxed_6321_ = lean_unbox(v_t_6318_);
v_res_6322_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6317_, v_t_boxed_6321_, v_h_6319_, v_nonDependentOnly_6320_);
lean_dec(v_nonDependentOnly_6320_);
return v_res_6322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6323_){
_start:
{
lean_inc(v_all_6323_);
return v_all_6323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6324_){
_start:
{
lean_object* v_res_6325_; 
v_res_6325_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6324_);
lean_dec(v_all_6324_);
return v_res_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6326_, uint8_t v_t_6327_, lean_object* v_h_6328_, lean_object* v_all_6329_){
_start:
{
lean_inc(v_all_6329_);
return v_all_6329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6330_, lean_object* v_t_6331_, lean_object* v_h_6332_, lean_object* v_all_6333_){
_start:
{
uint8_t v_t_boxed_6334_; lean_object* v_res_6335_; 
v_t_boxed_6334_ = lean_unbox(v_t_6331_);
v_res_6335_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6330_, v_t_boxed_6334_, v_h_6332_, v_all_6333_);
lean_dec(v_all_6333_);
return v_res_6335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6349_){
_start:
{
lean_object* v___x_6350_; uint8_t v___x_6351_; 
v___x_6350_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6349_);
v___x_6351_ = l_Lean_Syntax_isOfKind(v_c_6349_, v___x_6350_);
if (v___x_6351_ == 0)
{
lean_object* v___x_6352_; uint8_t v___x_6353_; 
v___x_6352_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6349_);
v___x_6353_ = l_Lean_Syntax_isOfKind(v_c_6349_, v___x_6352_);
if (v___x_6353_ == 0)
{
lean_object* v___x_6354_; uint8_t v___x_6355_; 
v___x_6354_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6349_);
v___x_6355_ = l_Lean_Syntax_isOfKind(v_c_6349_, v___x_6354_);
if (v___x_6355_ == 0)
{
lean_object* v___x_6356_; 
lean_dec(v_c_6349_);
v___x_6356_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6356_;
}
else
{
lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6357_ = lean_unsigned_to_nat(1u);
v___x_6358_ = lean_mk_empty_array_with_capacity(v___x_6357_);
v___x_6359_ = lean_array_push(v___x_6358_, v_c_6349_);
return v___x_6359_;
}
}
else
{
lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; 
v___x_6360_ = lean_unsigned_to_nat(0u);
v___x_6361_ = l_Lean_Syntax_getArg(v_c_6349_, v___x_6360_);
lean_dec(v_c_6349_);
v___x_6362_ = l_Lean_Syntax_getArgs(v___x_6361_);
lean_dec(v___x_6361_);
return v___x_6362_;
}
}
else
{
lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; uint8_t v___x_6367_; 
v___x_6363_ = l_Lean_Syntax_getArgs(v_c_6349_);
lean_dec(v_c_6349_);
v___x_6364_ = lean_unsigned_to_nat(0u);
v___x_6365_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6366_ = lean_array_get_size(v___x_6363_);
v___x_6367_ = lean_nat_dec_lt(v___x_6364_, v___x_6366_);
if (v___x_6367_ == 0)
{
lean_dec_ref(v___x_6363_);
return v___x_6365_;
}
else
{
size_t v___x_6368_; size_t v___x_6369_; lean_object* v___x_6370_; 
v___x_6368_ = ((size_t)0ULL);
v___x_6369_ = lean_usize_of_nat(v___x_6366_);
v___x_6370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6363_, v___x_6368_, v___x_6369_, v___x_6365_);
lean_dec_ref(v___x_6363_);
return v___x_6370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6371_, size_t v_i_6372_, size_t v_stop_6373_, lean_object* v_b_6374_){
_start:
{
uint8_t v___x_6375_; 
v___x_6375_ = lean_usize_dec_eq(v_i_6372_, v_stop_6373_);
if (v___x_6375_ == 0)
{
lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; size_t v___x_6379_; size_t v___x_6380_; 
v___x_6376_ = lean_array_uget_borrowed(v_as_6371_, v_i_6372_);
lean_inc(v___x_6376_);
v___x_6377_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6376_);
v___x_6378_ = l_Array_append___redArg(v_b_6374_, v___x_6377_);
lean_dec_ref(v___x_6377_);
v___x_6379_ = ((size_t)1ULL);
v___x_6380_ = lean_usize_add(v_i_6372_, v___x_6379_);
v_i_6372_ = v___x_6380_;
v_b_6374_ = v___x_6378_;
goto _start;
}
else
{
return v_b_6374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6382_, lean_object* v_i_6383_, lean_object* v_stop_6384_, lean_object* v_b_6385_){
_start:
{
size_t v_i_boxed_6386_; size_t v_stop_boxed_6387_; lean_object* v_res_6388_; 
v_i_boxed_6386_ = lean_unbox_usize(v_i_6383_);
lean_dec(v_i_6383_);
v_stop_boxed_6387_ = lean_unbox_usize(v_stop_6384_);
lean_dec(v_stop_6384_);
v_res_6388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6382_, v_i_boxed_6386_, v_stop_boxed_6387_, v_b_6385_);
lean_dec_ref(v_as_6382_);
return v_res_6388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6389_){
_start:
{
lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; 
v___x_6390_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6391_ = lean_box(2);
v___x_6392_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6393_, 0, v___x_6391_);
lean_ctor_set(v___x_6393_, 1, v___x_6392_);
lean_ctor_set(v___x_6393_, 2, v_items_6389_);
v___x_6394_ = l_Lean_Syntax_node1(v___x_6391_, v___x_6390_, v___x_6393_);
return v___x_6394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6395_, lean_object* v_cfg_x27_6396_){
_start:
{
lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; 
v___x_6397_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6395_);
v___x_6398_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6396_);
v___x_6399_ = l_Array_append___redArg(v___x_6397_, v___x_6398_);
lean_dec_ref(v___x_6398_);
v___x_6400_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6399_);
return v___x_6400_;
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
