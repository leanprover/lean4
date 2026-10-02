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
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 945;
v___x_168_ = lean_uint32_dec_le(v___x_167_, v_c_123_);
if (v___x_168_ == 0)
{
goto v___jp_158_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 969;
v___x_170_ = lean_uint32_dec_le(v_c_123_, v___x_169_);
if (v___x_170_ == 0)
{
goto v___jp_158_;
}
else
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 955;
v___x_172_ = lean_uint32_dec_eq(v_c_123_, v___x_171_);
if (v___x_172_ == 0)
{
if (v___x_170_ == 0)
{
goto v___jp_158_;
}
else
{
return v___x_170_;
}
}
else
{
goto v___jp_158_;
}
}
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
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 192;
v___x_131_ = lean_uint32_dec_le(v___x_130_, v_c_123_);
if (v___x_131_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 255;
v___x_133_ = lean_uint32_dec_le(v_c_123_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 215;
v___x_135_ = lean_uint32_dec_eq(v_c_123_, v___x_134_);
if (v___x_135_ == 0)
{
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 247;
v___x_137_ = lean_uint32_dec_eq(v_c_123_, v___x_136_);
if (v___x_137_ == 0)
{
return v___x_133_;
}
else
{
goto v___jp_124_;
}
}
}
else
{
goto v___jp_124_;
}
}
}
}
v___jp_138_:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 119964;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v_c_123_);
if (v___x_140_ == 0)
{
goto v___jp_129_;
}
else
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 120223;
v___x_142_ = lean_uint32_dec_le(v_c_123_, v___x_141_);
if (v___x_142_ == 0)
{
goto v___jp_129_;
}
else
{
return v___x_142_;
}
}
}
v___jp_143_:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 8448;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_123_);
if (v___x_145_ == 0)
{
goto v___jp_138_;
}
else
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 8527;
v___x_147_ = lean_uint32_dec_le(v_c_123_, v___x_146_);
if (v___x_147_ == 0)
{
goto v___jp_138_;
}
else
{
return v___x_147_;
}
}
}
v___jp_148_:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 7936;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_123_);
if (v___x_150_ == 0)
{
goto v___jp_143_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 8190;
v___x_152_ = lean_uint32_dec_le(v_c_123_, v___x_151_);
if (v___x_152_ == 0)
{
goto v___jp_143_;
}
else
{
return v___x_152_;
}
}
}
v___jp_153_:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 970;
v___x_155_ = lean_uint32_dec_le(v___x_154_, v_c_123_);
if (v___x_155_ == 0)
{
goto v___jp_148_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 1019;
v___x_157_ = lean_uint32_dec_le(v_c_123_, v___x_156_);
if (v___x_157_ == 0)
{
goto v___jp_148_;
}
else
{
return v___x_157_;
}
}
}
v___jp_158_:
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 913;
v___x_160_ = lean_uint32_dec_le(v___x_159_, v_c_123_);
if (v___x_160_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 937;
v___x_162_ = lean_uint32_dec_le(v_c_123_, v___x_161_);
if (v___x_162_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 928;
v___x_164_ = lean_uint32_dec_eq(v_c_123_, v___x_163_);
if (v___x_164_ == 0)
{
if (v___x_162_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 931;
v___x_166_ = lean_uint32_dec_eq(v_c_123_, v___x_165_);
if (v___x_166_ == 0)
{
return v___x_162_;
}
else
{
goto v___jp_153_;
}
}
}
else
{
goto v___jp_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_173_){
_start:
{
uint32_t v_c_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_c_boxed_174_ = lean_unbox_uint32(v_c_173_);
lean_dec(v_c_173_);
v_res_175_ = l_Lean_isLetterLike(v_c_boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t v_c_177_){
_start:
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 8320;
v___x_179_ = lean_uint32_dec_le(v___x_178_, v_c_177_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 8329;
v___x_181_ = lean_uint32_dec_le(v_c_177_, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_182_){
_start:
{
uint32_t v_c_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_c_boxed_183_ = lean_unbox_uint32(v_c_182_);
lean_dec(v_c_182_);
v_res_184_ = l_Lean_isNumericSubscript(v_c_boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_186_){
_start:
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 8320;
v___x_201_ = lean_uint32_dec_le(v___x_200_, v_c_186_);
if (v___x_201_ == 0)
{
goto v___jp_195_;
}
else
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 8329;
v___x_203_ = lean_uint32_dec_le(v_c_186_, v___x_202_);
if (v___x_203_ == 0)
{
goto v___jp_195_;
}
else
{
return v___x_203_;
}
}
v___jp_187_:
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 11388;
v___x_189_ = lean_uint32_dec_eq(v_c_186_, v___x_188_);
return v___x_189_;
}
v___jp_190_:
{
uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 7522;
v___x_192_ = lean_uint32_dec_le(v___x_191_, v_c_186_);
if (v___x_192_ == 0)
{
goto v___jp_187_;
}
else
{
uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 7530;
v___x_194_ = lean_uint32_dec_le(v_c_186_, v___x_193_);
if (v___x_194_ == 0)
{
goto v___jp_187_;
}
else
{
return v___x_194_;
}
}
}
v___jp_195_:
{
uint32_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = 8336;
v___x_197_ = lean_uint32_dec_le(v___x_196_, v_c_186_);
if (v___x_197_ == 0)
{
goto v___jp_190_;
}
else
{
uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = 8348;
v___x_199_ = lean_uint32_dec_le(v_c_186_, v___x_198_);
if (v___x_199_ == 0)
{
goto v___jp_190_;
}
else
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_204_){
_start:
{
uint32_t v_c_boxed_205_; uint8_t v_res_206_; lean_object* v_r_207_; 
v_c_boxed_205_ = lean_unbox_uint32(v_c_204_);
lean_dec(v_c_204_);
v_res_206_ = l_Lean_isSubScriptAlnum(v_c_boxed_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t v_c_208_){
_start:
{
uint8_t v___y_214_; uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 65;
v___x_220_ = lean_uint32_dec_le(v___x_219_, v_c_208_);
if (v___x_220_ == 0)
{
v___y_214_ = v___x_220_;
goto v___jp_213_;
}
else
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 90;
v___x_222_ = lean_uint32_dec_le(v_c_208_, v___x_221_);
v___y_214_ = v___x_222_;
goto v___jp_213_;
}
v___jp_209_:
{
uint32_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 95;
v___x_211_ = lean_uint32_dec_eq(v_c_208_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_isLetterLike(v_c_208_);
return v___x_212_;
}
else
{
return v___x_211_;
}
}
v___jp_213_:
{
if (v___y_214_ == 0)
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 97;
v___x_216_ = lean_uint32_dec_le(v___x_215_, v_c_208_);
if (v___x_216_ == 0)
{
goto v___jp_209_;
}
else
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 122;
v___x_218_ = lean_uint32_dec_le(v_c_208_, v___x_217_);
if (v___x_218_ == 0)
{
goto v___jp_209_;
}
else
{
return v___x_218_;
}
}
}
else
{
return v___y_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_223_){
_start:
{
uint32_t v_c_boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_c_boxed_224_ = lean_unbox_uint32(v_c_223_);
lean_dec(v_c_223_);
v_res_225_ = l_Lean_isIdFirst(v_c_boxed_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0(void){
_start:
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 65;
v___x_228_ = lean_uint32_to_uint8(v___x_227_);
return v___x_228_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1(void){
_start:
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 90;
v___x_230_ = lean_uint32_to_uint8(v___x_229_);
return v___x_230_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2(void){
_start:
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 97;
v___x_232_ = lean_uint32_to_uint8(v___x_231_);
return v___x_232_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3(void){
_start:
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 122;
v___x_234_ = lean_uint32_to_uint8(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_235_){
_start:
{
uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_242_ = lean_uint8_dec_le(v___x_241_, v_c_235_);
if (v___x_242_ == 0)
{
goto v___jp_236_;
}
else
{
uint8_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_244_ = lean_uint8_dec_le(v_c_235_, v___x_243_);
if (v___x_244_ == 0)
{
goto v___jp_236_;
}
else
{
return v___x_244_;
}
}
v___jp_236_:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_238_ = lean_uint8_dec_le(v___x_237_, v_c_235_);
if (v___x_238_ == 0)
{
return v___x_238_;
}
else
{
uint8_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_240_ = lean_uint8_dec_le(v_c_235_, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_245_){
_start:
{
uint8_t v_c_boxed_246_; uint8_t v_res_247_; lean_object* v_r_248_; 
v_c_boxed_246_ = lean_unbox(v_c_245_);
v_res_247_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0(void){
_start:
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 95;
v___x_250_ = lean_uint32_to_uint8(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_251_){
_start:
{
uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_261_ = lean_uint8_dec_le(v___x_260_, v_c_251_);
if (v___x_261_ == 0)
{
goto v___jp_255_;
}
else
{
uint8_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_263_ = lean_uint8_dec_le(v_c_251_, v___x_262_);
if (v___x_263_ == 0)
{
goto v___jp_255_;
}
else
{
return v___x_263_;
}
}
v___jp_252_:
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_254_ = lean_uint8_dec_eq(v_c_251_, v___x_253_);
return v___x_254_;
}
v___jp_255_:
{
uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_257_ = lean_uint8_dec_le(v___x_256_, v_c_251_);
if (v___x_257_ == 0)
{
goto v___jp_252_;
}
else
{
uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_259_ = lean_uint8_dec_le(v_c_251_, v___x_258_);
if (v___x_259_ == 0)
{
goto v___jp_252_;
}
else
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_264_){
_start:
{
uint8_t v_c_boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_c_boxed_265_ = lean_unbox(v_c_264_);
v_res_266_ = l_Lean_isIdFirstAscii(v_c_boxed_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0(void){
_start:
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 48;
v___x_269_ = lean_uint32_to_uint8(v___x_268_);
return v___x_269_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1(void){
_start:
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 57;
v___x_271_ = lean_uint32_to_uint8(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_272_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_272_);
if (v___x_284_ == 0)
{
goto v___jp_278_;
}
else
{
uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_286_ = lean_uint8_dec_le(v_c_272_, v___x_285_);
if (v___x_286_ == 0)
{
goto v___jp_278_;
}
else
{
return v___x_286_;
}
}
v___jp_273_:
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_275_ = lean_uint8_dec_le(v___x_274_, v_c_272_);
if (v___x_275_ == 0)
{
return v___x_275_;
}
else
{
uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_277_ = lean_uint8_dec_le(v_c_272_, v___x_276_);
return v___x_277_;
}
}
v___jp_278_:
{
uint8_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_280_ = lean_uint8_dec_le(v___x_279_, v_c_272_);
if (v___x_280_ == 0)
{
goto v___jp_273_;
}
else
{
uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_282_ = lean_uint8_dec_le(v_c_272_, v___x_281_);
if (v___x_282_ == 0)
{
goto v___jp_273_;
}
else
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_287_){
_start:
{
uint8_t v_c_boxed_288_; uint8_t v_res_289_; lean_object* v_r_290_; 
v_c_boxed_288_ = lean_unbox(v_c_287_);
v_res_289_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_291_){
_start:
{
uint8_t v___y_309_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 65;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v_c_291_);
if (v___x_315_ == 0)
{
v___y_309_ = v___x_315_;
goto v___jp_308_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 90;
v___x_317_ = lean_uint32_dec_le(v_c_291_, v___x_316_);
v___y_309_ = v___x_317_;
goto v___jp_308_;
}
v___jp_292_:
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 95;
v___x_294_ = lean_uint32_dec_eq(v_c_291_, v___x_293_);
if (v___x_294_ == 0)
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 39;
v___x_296_ = lean_uint32_dec_eq(v_c_291_, v___x_295_);
if (v___x_296_ == 0)
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 33;
v___x_298_ = lean_uint32_dec_eq(v_c_291_, v___x_297_);
if (v___x_298_ == 0)
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 63;
v___x_300_ = lean_uint32_dec_eq(v_c_291_, v___x_299_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_isLetterLike(v_c_291_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_isSubScriptAlnum(v_c_291_);
return v___x_302_;
}
else
{
return v___x_301_;
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
else
{
return v___x_296_;
}
}
else
{
return v___x_294_;
}
}
v___jp_303_:
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 48;
v___x_305_ = lean_uint32_dec_le(v___x_304_, v_c_291_);
if (v___x_305_ == 0)
{
goto v___jp_292_;
}
else
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 57;
v___x_307_ = lean_uint32_dec_le(v_c_291_, v___x_306_);
if (v___x_307_ == 0)
{
goto v___jp_292_;
}
else
{
return v___x_307_;
}
}
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 97;
v___x_311_ = lean_uint32_dec_le(v___x_310_, v_c_291_);
if (v___x_311_ == 0)
{
goto v___jp_303_;
}
else
{
uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 122;
v___x_313_ = lean_uint32_dec_le(v_c_291_, v___x_312_);
if (v___x_313_ == 0)
{
goto v___jp_303_;
}
else
{
return v___x_313_;
}
}
}
else
{
return v___y_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_318_){
_start:
{
uint32_t v_c_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_c_boxed_319_ = lean_unbox_uint32(v_c_318_);
lean_dec(v_c_318_);
v_res_320_ = l_Lean_isIdRest(v_c_boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0(void){
_start:
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 39;
v___x_323_ = lean_uint32_to_uint8(v___x_322_);
return v___x_323_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1(void){
_start:
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 33;
v___x_325_ = lean_uint32_to_uint8(v___x_324_);
return v___x_325_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2(void){
_start:
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 63;
v___x_327_ = lean_uint32_to_uint8(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_328_){
_start:
{
uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_349_ = lean_uint8_dec_le(v___x_348_, v_c_328_);
if (v___x_349_ == 0)
{
goto v___jp_343_;
}
else
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_351_ = lean_uint8_dec_le(v_c_328_, v___x_350_);
if (v___x_351_ == 0)
{
goto v___jp_343_;
}
else
{
return v___x_351_;
}
}
v___jp_329_:
{
uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_331_ = lean_uint8_dec_eq(v_c_328_, v___x_330_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_333_ = lean_uint8_dec_eq(v_c_328_, v___x_332_);
if (v___x_333_ == 0)
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_335_ = lean_uint8_dec_eq(v_c_328_, v___x_334_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_337_ = lean_uint8_dec_eq(v_c_328_, v___x_336_);
return v___x_337_;
}
else
{
return v___x_335_;
}
}
else
{
return v___x_333_;
}
}
else
{
return v___x_331_;
}
}
v___jp_338_:
{
uint8_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_340_ = lean_uint8_dec_le(v___x_339_, v_c_328_);
if (v___x_340_ == 0)
{
goto v___jp_329_;
}
else
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_342_ = lean_uint8_dec_le(v_c_328_, v___x_341_);
if (v___x_342_ == 0)
{
goto v___jp_329_;
}
else
{
return v___x_342_;
}
}
}
v___jp_343_:
{
uint8_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_345_ = lean_uint8_dec_le(v___x_344_, v_c_328_);
if (v___x_345_ == 0)
{
goto v___jp_338_;
}
else
{
uint8_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_347_ = lean_uint8_dec_le(v_c_328_, v___x_346_);
if (v___x_347_ == 0)
{
goto v___jp_338_;
}
else
{
return v___x_347_;
}
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_358_){
_start:
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 171;
v___x_360_ = lean_uint32_dec_eq(v_c_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_361_){
_start:
{
uint32_t v_c_boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v_c_boxed_362_ = lean_unbox_uint32(v_c_361_);
lean_dec(v_c_361_);
v_res_363_ = l_Lean_isIdBeginEscape(v_c_boxed_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_365_){
_start:
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 187;
v___x_367_ = lean_uint32_dec_eq(v_c_365_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_368_){
_start:
{
uint32_t v_c_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_c_boxed_369_ = lean_unbox_uint32(v_c_368_);
lean_dec(v_c_368_);
v_res_370_ = l_Lean_isIdEndEscape(v_c_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
return v_x_372_;
}
else
{
lean_object* v_pre_373_; 
v_pre_373_ = lean_ctor_get(v_x_372_, 0);
if (lean_obj_tag(v_pre_373_) == 0)
{
lean_inc(v_x_372_);
return v_x_372_;
}
else
{
v_x_372_ = v_pre_373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Name_getRoot(v_x_375_);
lean_dec(v_x_375_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_378_){
_start:
{
switch(lean_obj_tag(v_x_378_))
{
case 1:
{
lean_object* v_str_379_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_str_379_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref_n(v_str_379_, 2);
lean_dec_ref_known(v_x_378_, 2);
v___x_380_ = 10013;
v___x_381_ = lean_string_contains(v_str_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_383_ = lean_string_dec_eq(v_str_379_, v___x_382_);
lean_dec_ref(v_str_379_);
return v___x_383_;
}
else
{
lean_dec_ref(v_str_379_);
return v___x_381_;
}
}
case 2:
{
lean_object* v_pre_384_; 
v_pre_384_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_pre_384_);
lean_dec_ref_known(v_x_378_, 2);
v_x_378_ = v_pre_384_;
goto _start;
}
default: 
{
uint8_t v___x_386_; 
lean_dec(v_x_378_);
v___x_386_ = 0;
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Name_isInaccessibleUserName(v_x_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_390_, lean_object* v_i_391_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_string_utf8_byte_size(v_s_390_);
v___x_397_ = lean_nat_dec_lt(v_i_391_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; 
lean_dec(v_i_391_);
v___x_398_ = 1;
return v___x_398_;
}
else
{
uint8_t v_c_399_; uint8_t v___x_419_; uint8_t v___x_420_; 
lean_inc(v_i_391_);
v_c_399_ = lean_string_get_byte_fast(v_s_390_, v_i_391_);
v___x_419_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_c_399_);
if (v___x_420_ == 0)
{
goto v___jp_414_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_422_ = lean_uint8_dec_le(v_c_399_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_414_;
}
else
{
goto v___jp_392_;
}
}
v___jp_400_:
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_402_ = lean_uint8_dec_eq(v_c_399_, v___x_401_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_404_ = lean_uint8_dec_eq(v_c_399_, v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_406_ = lean_uint8_dec_eq(v_c_399_, v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_408_ = lean_uint8_dec_eq(v_c_399_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v_i_391_);
return v___x_408_;
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
v___jp_409_:
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_411_ = lean_uint8_dec_le(v___x_410_, v_c_399_);
if (v___x_411_ == 0)
{
goto v___jp_400_;
}
else
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_413_ = lean_uint8_dec_le(v_c_399_, v___x_412_);
if (v___x_413_ == 0)
{
goto v___jp_400_;
}
else
{
goto v___jp_392_;
}
}
}
v___jp_414_:
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_416_ = lean_uint8_dec_le(v___x_415_, v_c_399_);
if (v___x_416_ == 0)
{
goto v___jp_409_;
}
else
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_418_ = lean_uint8_dec_le(v_c_399_, v___x_417_);
if (v___x_418_ == 0)
{
goto v___jp_409_;
}
else
{
goto v___jp_392_;
}
}
}
}
v___jp_392_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_i_391_, v___x_393_);
lean_dec(v_i_391_);
v_i_391_ = v___x_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_423_, lean_object* v_i_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_423_, v_i_424_);
lean_dec_ref(v_s_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_427_){
_start:
{
lean_object* v___x_431_; uint8_t v_c_432_; uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v_c_432_ = lean_string_get_byte_fast(v_s_427_, v___x_431_);
v___x_441_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_442_ = lean_uint8_dec_le(v___x_441_, v_c_432_);
if (v___x_442_ == 0)
{
goto v___jp_436_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_444_ = lean_uint8_dec_le(v_c_432_, v___x_443_);
if (v___x_444_ == 0)
{
goto v___jp_436_;
}
else
{
goto v___jp_428_;
}
}
v___jp_428_:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_427_, v___x_429_);
return v___x_430_;
}
v___jp_433_:
{
uint8_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_435_ = lean_uint8_dec_eq(v_c_432_, v___x_434_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
goto v___jp_428_;
}
}
v___jp_436_:
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_438_ = lean_uint8_dec_le(v___x_437_, v_c_432_);
if (v___x_438_ == 0)
{
goto v___jp_433_;
}
else
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_440_ = lean_uint8_dec_le(v_c_432_, v___x_439_);
if (v___x_440_ == 0)
{
goto v___jp_433_;
}
else
{
goto v___jp_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_445_);
lean_dec_ref(v_s_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_448_, lean_object* v_h_449_){
_start:
{
lean_object* v___x_453_; uint8_t v_c_454_; uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v_c_454_ = lean_string_get_byte_fast(v_s_448_, v___x_453_);
v___x_463_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_464_ = lean_uint8_dec_le(v___x_463_, v_c_454_);
if (v___x_464_ == 0)
{
goto v___jp_458_;
}
else
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_466_ = lean_uint8_dec_le(v_c_454_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_458_;
}
else
{
goto v___jp_450_;
}
}
v___jp_450_:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_448_, v___x_451_);
return v___x_452_;
}
v___jp_455_:
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_457_ = lean_uint8_dec_eq(v_c_454_, v___x_456_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
goto v___jp_450_;
}
}
v___jp_458_:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_460_ = lean_uint8_dec_le(v___x_459_, v_c_454_);
if (v___x_460_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_462_ = lean_uint8_dec_le(v_c_454_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_455_;
}
else
{
goto v___jp_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_467_, lean_object* v_h_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_467_, v_h_468_);
lean_dec_ref(v_s_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_472_){
_start:
{
uint32_t v___y_482_; uint32_t v___y_487_; uint8_t v___y_488_; lean_object* v___x_503_; uint8_t v_c_504_; uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v_c_504_ = lean_string_get_byte_fast(v_s_472_, v___x_503_);
v___x_513_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_514_ = lean_uint8_dec_le(v___x_513_, v_c_504_);
if (v___x_514_ == 0)
{
goto v___jp_508_;
}
else
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_516_ = lean_uint8_dec_le(v_c_504_, v___x_515_);
if (v___x_516_ == 0)
{
goto v___jp_508_;
}
else
{
goto v___jp_500_;
}
}
v___jp_473_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_string_utf8_byte_size(v_s_472_);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_s_472_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_substring_drop(v___x_476_, v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_480_ = lean_substring_all(v___x_478_, v___x_479_);
return v___x_480_;
}
v___jp_481_:
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 95;
v___x_484_ = lean_uint32_dec_eq(v___y_482_, v___x_483_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; 
v___x_485_ = l_Lean_isLetterLike(v___y_482_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_s_472_);
return v___x_485_;
}
else
{
goto v___jp_473_;
}
}
else
{
goto v___jp_473_;
}
}
v___jp_486_:
{
if (v___y_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 97;
v___x_490_ = lean_uint32_dec_le(v___x_489_, v___y_487_);
if (v___x_490_ == 0)
{
v___y_482_ = v___y_487_;
goto v___jp_481_;
}
else
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 122;
v___x_492_ = lean_uint32_dec_le(v___y_487_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_482_ = v___y_487_;
goto v___jp_481_;
}
else
{
goto v___jp_473_;
}
}
}
else
{
goto v___jp_473_;
}
}
v___jp_493_:
{
lean_object* v___x_494_; uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_string_utf8_get(v_s_472_, v___x_494_);
v___x_496_ = 65;
v___x_497_ = lean_uint32_dec_le(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
v___y_487_ = v___x_495_;
v___y_488_ = v___x_497_;
goto v___jp_486_;
}
else
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 90;
v___x_499_ = lean_uint32_dec_le(v___x_495_, v___x_498_);
v___y_487_ = v___x_495_;
v___y_488_ = v___x_499_;
goto v___jp_486_;
}
}
v___jp_500_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_472_, v___x_501_);
if (v___x_502_ == 0)
{
goto v___jp_493_;
}
else
{
lean_dec_ref(v_s_472_);
return v___x_502_;
}
}
v___jp_505_:
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_507_ = lean_uint8_dec_eq(v_c_504_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_493_;
}
else
{
goto v___jp_500_;
}
}
v___jp_508_:
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_510_ = lean_uint8_dec_le(v___x_509_, v_c_504_);
if (v___x_510_ == 0)
{
goto v___jp_505_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_512_ = lean_uint8_dec_le(v_c_504_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_505_;
}
else
{
goto v___jp_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_517_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_520_, lean_object* v_h_521_){
_start:
{
uint32_t v___y_531_; uint32_t v___y_536_; uint8_t v___y_537_; lean_object* v___x_552_; uint8_t v_c_553_; uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v_c_553_ = lean_string_get_byte_fast(v_s_520_, v___x_552_);
v___x_562_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_563_ = lean_uint8_dec_le(v___x_562_, v_c_553_);
if (v___x_563_ == 0)
{
goto v___jp_557_;
}
else
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_565_ = lean_uint8_dec_le(v_c_553_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_557_;
}
else
{
goto v___jp_549_;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_byte_size(v_s_520_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_s_520_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_substring_drop(v___x_525_, v___x_526_);
v___x_528_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_529_ = lean_substring_all(v___x_527_, v___x_528_);
return v___x_529_;
}
v___jp_530_:
{
uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = 95;
v___x_533_ = lean_uint32_dec_eq(v___y_531_, v___x_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_isLetterLike(v___y_531_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_s_520_);
return v___x_534_;
}
else
{
goto v___jp_522_;
}
}
else
{
goto v___jp_522_;
}
}
v___jp_535_:
{
if (v___y_537_ == 0)
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 97;
v___x_539_ = lean_uint32_dec_le(v___x_538_, v___y_536_);
if (v___x_539_ == 0)
{
v___y_531_ = v___y_536_;
goto v___jp_530_;
}
else
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 122;
v___x_541_ = lean_uint32_dec_le(v___y_536_, v___x_540_);
if (v___x_541_ == 0)
{
v___y_531_ = v___y_536_;
goto v___jp_530_;
}
else
{
goto v___jp_522_;
}
}
}
else
{
goto v___jp_522_;
}
}
v___jp_542_:
{
lean_object* v___x_543_; uint32_t v___x_544_; uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_string_utf8_get(v_s_520_, v___x_543_);
v___x_545_ = 65;
v___x_546_ = lean_uint32_dec_le(v___x_545_, v___x_544_);
if (v___x_546_ == 0)
{
v___y_536_ = v___x_544_;
v___y_537_ = v___x_546_;
goto v___jp_535_;
}
else
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 90;
v___x_548_ = lean_uint32_dec_le(v___x_544_, v___x_547_);
v___y_536_ = v___x_544_;
v___y_537_ = v___x_548_;
goto v___jp_535_;
}
}
v___jp_549_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_520_, v___x_550_);
if (v___x_551_ == 0)
{
goto v___jp_542_;
}
else
{
lean_dec_ref(v_s_520_);
return v___x_551_;
}
}
v___jp_554_:
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_556_ = lean_uint8_dec_eq(v_c_553_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_542_;
}
else
{
goto v___jp_549_;
}
}
v___jp_557_:
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_559_ = lean_uint8_dec_le(v___x_558_, v_c_553_);
if (v___x_559_ == 0)
{
goto v___jp_554_;
}
else
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_561_ = lean_uint8_dec_le(v_c_553_, v___x_560_);
if (v___x_561_ == 0)
{
goto v___jp_554_;
}
else
{
goto v___jp_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_566_, lean_object* v_h_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_566_, v_h_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0(void){
_start:
{
uint32_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = 171;
v___x_571_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_572_ = lean_string_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = 187;
v___x_574_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_575_ = lean_string_push(v___x_574_, v___x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_578_ = lean_string_append(v___x_577_, v_s_576_);
v___x_579_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_581_);
lean_dec_ref(v_s_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_584_, uint8_t v_force_585_){
_start:
{
uint8_t v___y_596_; uint32_t v___y_607_; uint32_t v___y_612_; uint8_t v___y_613_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_string_utf8_byte_size(v_s_584_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_632_ = lean_string_append(v___x_631_, v_s_584_);
lean_dec_ref(v_s_584_);
v___x_633_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
if (v_force_585_ == 0)
{
uint8_t v_c_636_; uint8_t v___x_645_; uint8_t v___x_646_; 
v_c_636_ = lean_string_get_byte_fast(v_s_584_, v___x_628_);
v___x_645_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_646_ = lean_uint8_dec_le(v___x_645_, v_c_636_);
if (v___x_646_ == 0)
{
goto v___jp_640_;
}
else
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_648_ = lean_uint8_dec_le(v_c_636_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_640_;
}
else
{
goto v___jp_625_;
}
}
v___jp_637_:
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_639_ = lean_uint8_dec_eq(v_c_636_, v___x_638_);
if (v___x_639_ == 0)
{
goto v___jp_618_;
}
else
{
goto v___jp_625_;
}
}
v___jp_640_:
{
uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_642_ = lean_uint8_dec_le(v___x_641_, v_c_636_);
if (v___x_642_ == 0)
{
goto v___jp_637_;
}
else
{
uint8_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_644_ = lean_uint8_dec_le(v_c_636_, v___x_643_);
if (v___x_644_ == 0)
{
goto v___jp_637_;
}
else
{
goto v___jp_625_;
}
}
}
}
else
{
goto v___jp_586_;
}
}
v___jp_586_:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_584_);
v___x_588_ = lean_string_any(v_s_584_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_590_ = lean_string_append(v___x_589_, v_s_584_);
lean_dec_ref(v_s_584_);
v___x_591_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
lean_dec_ref(v_s_584_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
goto v___jp_586_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_s_584_);
return v___x_597_;
}
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_string_utf8_byte_size(v_s_584_);
lean_inc_ref(v_s_584_);
v___x_601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_601_, 0, v_s_584_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_substring_drop(v___x_601_, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_605_ = lean_substring_all(v___x_603_, v___x_604_);
v___y_596_ = v___x_605_;
goto v___jp_595_;
}
v___jp_606_:
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 95;
v___x_609_ = lean_uint32_dec_eq(v___y_607_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
v___x_610_ = l_Lean_isLetterLike(v___y_607_);
if (v___x_610_ == 0)
{
v___y_596_ = v___x_610_;
goto v___jp_595_;
}
else
{
goto v___jp_598_;
}
}
else
{
goto v___jp_598_;
}
}
v___jp_611_:
{
if (v___y_613_ == 0)
{
uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 97;
v___x_615_ = lean_uint32_dec_le(v___x_614_, v___y_612_);
if (v___x_615_ == 0)
{
v___y_607_ = v___y_612_;
goto v___jp_606_;
}
else
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 122;
v___x_617_ = lean_uint32_dec_le(v___y_612_, v___x_616_);
if (v___x_617_ == 0)
{
v___y_607_ = v___y_612_;
goto v___jp_606_;
}
else
{
goto v___jp_598_;
}
}
}
else
{
goto v___jp_598_;
}
}
v___jp_618_:
{
lean_object* v___x_619_; uint32_t v___x_620_; uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_string_utf8_get(v_s_584_, v___x_619_);
v___x_621_ = 65;
v___x_622_ = lean_uint32_dec_le(v___x_621_, v___x_620_);
if (v___x_622_ == 0)
{
v___y_612_ = v___x_620_;
v___y_613_ = v___x_622_;
goto v___jp_611_;
}
else
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 90;
v___x_624_ = lean_uint32_dec_le(v___x_620_, v___x_623_);
v___y_612_ = v___x_620_;
v___y_613_ = v___x_624_;
goto v___jp_611_;
}
}
v___jp_625_:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_584_, v___x_626_);
if (v___x_627_ == 0)
{
goto v___jp_618_;
}
else
{
v___y_596_ = v___x_627_;
goto v___jp_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_649_, lean_object* v_force_650_){
_start:
{
uint8_t v_force_boxed_651_; lean_object* v_res_652_; 
v_force_boxed_651_ = lean_unbox(v_force_650_);
v_res_652_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_649_, v_force_boxed_651_);
return v_res_652_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_653_){
_start:
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 187;
v___x_655_ = lean_uint32_dec_eq(v___y_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_656_){
_start:
{
uint32_t v___y_284__boxed_657_; uint8_t v_res_658_; lean_object* v_r_659_; 
v___y_284__boxed_657_ = lean_unbox_uint32(v___y_656_);
lean_dec(v___y_656_);
v_res_658_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_284__boxed_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_660_){
_start:
{
uint8_t v___y_678_; uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 65;
v___x_684_ = lean_uint32_dec_le(v___x_683_, v___y_660_);
if (v___x_684_ == 0)
{
v___y_678_ = v___x_684_;
goto v___jp_677_;
}
else
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 90;
v___x_686_ = lean_uint32_dec_le(v___y_660_, v___x_685_);
v___y_678_ = v___x_686_;
goto v___jp_677_;
}
v___jp_661_:
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 95;
v___x_663_ = lean_uint32_dec_eq(v___y_660_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 39;
v___x_665_ = lean_uint32_dec_eq(v___y_660_, v___x_664_);
if (v___x_665_ == 0)
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 33;
v___x_667_ = lean_uint32_dec_eq(v___y_660_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 63;
v___x_669_ = lean_uint32_dec_eq(v___y_660_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_isLetterLike(v___y_660_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_isSubScriptAlnum(v___y_660_);
return v___x_671_;
}
else
{
return v___x_670_;
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
else
{
return v___x_665_;
}
}
else
{
return v___x_663_;
}
}
v___jp_672_:
{
uint32_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 48;
v___x_674_ = lean_uint32_dec_le(v___x_673_, v___y_660_);
if (v___x_674_ == 0)
{
goto v___jp_661_;
}
else
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 57;
v___x_676_ = lean_uint32_dec_le(v___y_660_, v___x_675_);
if (v___x_676_ == 0)
{
goto v___jp_661_;
}
else
{
return v___x_676_;
}
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 97;
v___x_680_ = lean_uint32_dec_le(v___x_679_, v___y_660_);
if (v___x_680_ == 0)
{
goto v___jp_672_;
}
else
{
uint32_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 122;
v___x_682_ = lean_uint32_dec_le(v___y_660_, v___x_681_);
if (v___x_682_ == 0)
{
goto v___jp_672_;
}
else
{
return v___x_682_;
}
}
}
else
{
return v___y_678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_687_){
_start:
{
uint32_t v___y_291__boxed_688_; uint8_t v_res_689_; lean_object* v_r_690_; 
v___y_291__boxed_688_ = lean_unbox_uint32(v___y_687_);
lean_dec(v___y_687_);
v_res_689_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_291__boxed_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_693_, lean_object* v_s_694_, uint8_t v_force_695_){
_start:
{
if (v_escape_693_ == 0)
{
return v_s_694_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_string_utf8_byte_size(v_s_694_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_700_ = lean_string_append(v___x_699_, v_s_694_);
lean_dec_ref(v_s_694_);
v___x_701_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___f_703_; uint8_t v___y_711_; 
v___f_703_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_695_ == 0)
{
lean_object* v___f_712_; uint32_t v___y_719_; uint32_t v___y_724_; uint8_t v___y_725_; uint8_t v_c_739_; uint8_t v___x_748_; uint8_t v___x_749_; 
v___f_712_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_739_ = lean_string_get_byte_fast(v_s_694_, v___x_696_);
v___x_748_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_749_ = lean_uint8_dec_le(v___x_748_, v_c_739_);
if (v___x_749_ == 0)
{
goto v___jp_743_;
}
else
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_751_ = lean_uint8_dec_le(v_c_739_, v___x_750_);
if (v___x_751_ == 0)
{
goto v___jp_743_;
}
else
{
goto v___jp_736_;
}
}
v___jp_713_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
lean_inc_ref(v_s_694_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_s_694_);
lean_ctor_set(v___x_714_, 1, v___x_696_);
lean_ctor_set(v___x_714_, 2, v___x_697_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_substring_drop(v___x_714_, v___x_715_);
v___x_717_ = lean_substring_all(v___x_716_, v___f_712_);
v___y_711_ = v___x_717_;
goto v___jp_710_;
}
v___jp_718_:
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 95;
v___x_721_ = lean_uint32_dec_eq(v___y_719_, v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_isLetterLike(v___y_719_);
if (v___x_722_ == 0)
{
v___y_711_ = v___x_722_;
goto v___jp_710_;
}
else
{
goto v___jp_713_;
}
}
else
{
goto v___jp_713_;
}
}
v___jp_723_:
{
if (v___y_725_ == 0)
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 97;
v___x_727_ = lean_uint32_dec_le(v___x_726_, v___y_724_);
if (v___x_727_ == 0)
{
v___y_719_ = v___y_724_;
goto v___jp_718_;
}
else
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 122;
v___x_729_ = lean_uint32_dec_le(v___y_724_, v___x_728_);
if (v___x_729_ == 0)
{
v___y_719_ = v___y_724_;
goto v___jp_718_;
}
else
{
goto v___jp_713_;
}
}
}
else
{
goto v___jp_713_;
}
}
v___jp_730_:
{
uint32_t v___x_731_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_string_utf8_get(v_s_694_, v___x_696_);
v___x_732_ = 65;
v___x_733_ = lean_uint32_dec_le(v___x_732_, v___x_731_);
if (v___x_733_ == 0)
{
v___y_724_ = v___x_731_;
v___y_725_ = v___x_733_;
goto v___jp_723_;
}
else
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 90;
v___x_735_ = lean_uint32_dec_le(v___x_731_, v___x_734_);
v___y_724_ = v___x_731_;
v___y_725_ = v___x_735_;
goto v___jp_723_;
}
}
v___jp_736_:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_694_, v___x_737_);
if (v___x_738_ == 0)
{
goto v___jp_730_;
}
else
{
v___y_711_ = v___x_738_;
goto v___jp_710_;
}
}
v___jp_740_:
{
uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_742_ = lean_uint8_dec_eq(v_c_739_, v___x_741_);
if (v___x_742_ == 0)
{
goto v___jp_730_;
}
else
{
goto v___jp_736_;
}
}
v___jp_743_:
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_745_ = lean_uint8_dec_le(v___x_744_, v_c_739_);
if (v___x_745_ == 0)
{
goto v___jp_740_;
}
else
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_747_ = lean_uint8_dec_le(v_c_739_, v___x_746_);
if (v___x_747_ == 0)
{
goto v___jp_740_;
}
else
{
goto v___jp_736_;
}
}
}
}
else
{
goto v___jp_704_;
}
v___jp_704_:
{
uint8_t v___x_705_; 
lean_inc_ref(v_s_694_);
v___x_705_ = lean_string_any(v_s_694_, v___f_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_707_ = lean_string_append(v___x_706_, v_s_694_);
lean_dec_ref(v_s_694_);
v___x_708_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
return v___x_709_;
}
else
{
return v_s_694_;
}
}
v___jp_710_:
{
if (v___y_711_ == 0)
{
goto v___jp_704_;
}
else
{
return v_s_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_752_, lean_object* v_s_753_, lean_object* v_force_754_){
_start:
{
uint8_t v_escape_boxed_755_; uint8_t v_force_boxed_756_; lean_object* v_res_757_; 
v_escape_boxed_755_ = lean_unbox(v_escape_752_);
v_force_boxed_756_ = lean_unbox(v_force_754_);
v_res_757_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_755_, v_s_753_, v_force_boxed_756_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_760_);
lean_dec_ref(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_765_, uint8_t v_escape_766_, lean_object* v_n_767_, lean_object* v_isToken_768_){
_start:
{
switch(lean_obj_tag(v_n_767_))
{
case 0:
{
lean_object* v___x_769_; 
lean_dec_ref(v_isToken_768_);
v___x_769_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_769_;
}
case 1:
{
lean_object* v_pre_770_; 
v_pre_770_ = lean_ctor_get(v_n_767_, 0);
if (lean_obj_tag(v_pre_770_) == 0)
{
lean_object* v_str_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
v_str_771_ = lean_ctor_get(v_n_767_, 1);
lean_inc_ref_n(v_str_771_, 2);
lean_dec_ref_known(v_n_767_, 2);
v___x_772_ = lean_apply_1(v_isToken_768_, v_str_771_);
v___x_773_ = lean_unbox(v___x_772_);
v___x_774_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_771_, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_str_775_; lean_object* v_r_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v_r_x27_780_; 
lean_inc(v_pre_770_);
v_str_775_ = lean_ctor_get(v_n_767_, 1);
lean_inc_ref_n(v_str_775_, 2);
lean_dec_ref_known(v_n_767_, 2);
lean_inc_ref(v_isToken_768_);
v_r_776_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_765_, v_escape_766_, v_pre_770_, v_isToken_768_);
v___x_777_ = lean_string_append(v_r_776_, v_sep_765_);
v___x_778_ = 0;
v___x_779_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_775_, v___x_778_);
lean_inc_ref(v___x_777_);
v_r_x27_780_ = lean_string_append(v___x_777_, v___x_779_);
lean_dec_ref(v___x_779_);
if (v_escape_766_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_str_775_);
lean_dec_ref(v_isToken_768_);
return v_r_x27_780_;
}
else
{
lean_object* v___x_781_; uint8_t v___x_782_; 
lean_inc_ref(v_r_x27_780_);
v___x_781_ = lean_apply_1(v_isToken_768_, v_r_x27_780_);
v___x_782_ = lean_unbox(v___x_781_);
if (v___x_782_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_str_775_);
return v_r_x27_780_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_r_x27_780_);
v___x_783_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_775_, v_escape_766_);
v___x_784_ = lean_string_append(v___x_777_, v___x_783_);
lean_dec_ref(v___x_783_);
return v___x_784_;
}
}
}
}
default: 
{
lean_object* v_pre_785_; 
lean_dec_ref(v_isToken_768_);
v_pre_785_ = lean_ctor_get(v_n_767_, 0);
if (lean_obj_tag(v_pre_785_) == 0)
{
lean_object* v_i_786_; lean_object* v___x_787_; 
v_i_786_ = lean_ctor_get(v_n_767_, 1);
lean_inc(v_i_786_);
lean_dec_ref_known(v_n_767_, 2);
v___x_787_ = l_Nat_reprFast(v_i_786_);
return v___x_787_;
}
else
{
lean_object* v_i_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc(v_pre_785_);
v_i_788_ = lean_ctor_get(v_n_767_, 1);
lean_inc(v_i_788_);
lean_dec_ref_known(v_n_767_, 2);
v___f_789_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_790_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_765_, v_escape_766_, v_pre_785_, v___f_789_);
v___x_791_ = lean_string_append(v___x_790_, v_sep_765_);
v___x_792_ = l_Nat_reprFast(v_i_788_);
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
lean_dec_ref(v___x_792_);
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_794_, lean_object* v_escape_795_, lean_object* v_n_796_, lean_object* v_isToken_797_){
_start:
{
uint8_t v_escape_boxed_798_; lean_object* v_res_799_; 
v_escape_boxed_798_ = lean_unbox(v_escape_795_);
v_res_799_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_794_, v_escape_boxed_798_, v_n_796_, v_isToken_797_);
lean_dec_ref(v_sep_794_);
return v_res_799_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_806_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_807_ = lean_name_eq(v_n_805_, v___x_806_);
v___x_808_ = 1;
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Name_getRoot(v_n_805_);
if (lean_obj_tag(v___x_809_) == 1)
{
lean_object* v_str_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_str_810_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref_n(v_str_810_, 2);
lean_dec_ref_known(v___x_809_, 2);
v___x_811_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_812_ = lean_string_isprefixof(v___x_811_, v_str_810_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_814_ = lean_string_isprefixof(v___x_813_, v_str_810_);
return v___x_814_;
}
else
{
lean_dec_ref(v_str_810_);
return v___x_808_;
}
}
else
{
lean_dec(v___x_809_);
return v___x_807_;
}
}
else
{
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_815_);
lean_dec(v_n_815_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_818_, uint8_t v_escape_819_, lean_object* v_isToken_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_819_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v_escape_819_, v_n_818_, v_isToken_820_);
return v___x_822_;
}
else
{
uint8_t v___x_823_; 
lean_inc(v_n_818_);
v___x_823_ = l_Lean_Name_isInaccessibleUserName(v_n_818_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Name_hasMacroScopes(v_n_818_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_818_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v_escape_819_, v_n_818_, v_isToken_820_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_824_, v_n_818_, v_isToken_820_);
return v___x_827_;
}
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_823_, v_n_818_, v_isToken_820_);
return v___x_828_;
}
}
else
{
uint8_t v___x_829_; lean_object* v___x_830_; 
v___x_829_ = 0;
v___x_830_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_829_, v_n_818_, v_isToken_820_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_831_, lean_object* v_escape_832_, lean_object* v_isToken_833_){
_start:
{
uint8_t v_escape_boxed_834_; lean_object* v_res_835_; 
v_escape_boxed_834_ = lean_unbox(v_escape_832_);
v_res_835_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_831_, v_escape_boxed_834_, v_isToken_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_836_, uint8_t v_escape_837_, lean_object* v_n_838_){
_start:
{
switch(lean_obj_tag(v_n_838_))
{
case 0:
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_839_;
}
case 1:
{
lean_object* v_pre_840_; 
v_pre_840_ = lean_ctor_get(v_n_838_, 0);
if (lean_obj_tag(v_pre_840_) == 0)
{
lean_object* v_str_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_str_841_ = lean_ctor_get(v_n_838_, 1);
lean_inc_ref(v_str_841_);
lean_dec_ref_known(v_n_838_, 2);
v___x_842_ = 0;
v___x_843_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_837_, v_str_841_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v_str_844_; lean_object* v_r_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v_r_x27_849_; 
lean_inc(v_pre_840_);
v_str_844_ = lean_ctor_get(v_n_838_, 1);
lean_inc_ref(v_str_844_);
lean_dec_ref_known(v_n_838_, 2);
v_r_845_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_836_, v_escape_837_, v_pre_840_);
v___x_846_ = lean_string_append(v_r_845_, v_sep_836_);
v___x_847_ = 0;
v___x_848_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_837_, v_str_844_, v___x_847_);
v_r_x27_849_ = lean_string_append(v___x_846_, v___x_848_);
lean_dec_ref(v___x_848_);
return v_r_x27_849_;
}
}
default: 
{
lean_object* v_pre_850_; 
v_pre_850_ = lean_ctor_get(v_n_838_, 0);
if (lean_obj_tag(v_pre_850_) == 0)
{
lean_object* v_i_851_; lean_object* v___x_852_; 
v_i_851_ = lean_ctor_get(v_n_838_, 1);
lean_inc(v_i_851_);
lean_dec_ref_known(v_n_838_, 2);
v___x_852_ = l_Nat_reprFast(v_i_851_);
return v___x_852_;
}
else
{
lean_object* v_i_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc(v_pre_850_);
v_i_853_ = lean_ctor_get(v_n_838_, 1);
lean_inc(v_i_853_);
lean_dec_ref_known(v_n_838_, 2);
v___x_854_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_836_, v_escape_837_, v_pre_850_);
v___x_855_ = lean_string_append(v___x_854_, v_sep_836_);
v___x_856_ = l_Nat_reprFast(v_i_853_);
v___x_857_ = lean_string_append(v___x_855_, v___x_856_);
lean_dec_ref(v___x_856_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_858_, lean_object* v_escape_859_, lean_object* v_n_860_){
_start:
{
uint8_t v_escape_boxed_861_; lean_object* v_res_862_; 
v_escape_boxed_861_ = lean_unbox(v_escape_859_);
v_res_862_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_858_, v_escape_boxed_861_, v_n_860_);
lean_dec_ref(v_sep_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_863_, uint8_t v_escape_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_864_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v_escape_864_, v_n_863_);
return v___x_866_;
}
else
{
uint8_t v___x_867_; 
lean_inc(v_n_863_);
v___x_867_ = l_Lean_Name_isInaccessibleUserName(v_n_863_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_Name_hasMacroScopes(v_n_863_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_863_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v_escape_864_, v_n_863_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_868_, v_n_863_);
return v___x_871_;
}
}
else
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_867_, v_n_863_);
return v___x_872_;
}
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_873_ = 0;
v___x_874_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_873_, v_n_863_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_875_, lean_object* v_escape_876_){
_start:
{
uint8_t v_escape_boxed_877_; lean_object* v_res_878_; 
v_escape_boxed_877_ = lean_unbox(v_escape_876_);
v_res_878_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_875_, v_escape_boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_879_, uint8_t v_escape_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_879_, v_escape_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_882_, lean_object* v_escape_883_){
_start:
{
uint8_t v_escape_boxed_884_; lean_object* v_res_885_; 
v_escape_boxed_884_ = lean_unbox(v_escape_883_);
v_res_885_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_882_, v_escape_boxed_884_);
return v_res_885_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_886_){
_start:
{
switch(lean_obj_tag(v_x_886_))
{
case 0:
{
uint8_t v___x_887_; 
v___x_887_ = 0;
return v___x_887_;
}
case 1:
{
lean_object* v_pre_888_; 
v_pre_888_ = lean_ctor_get(v_x_886_, 0);
v_x_886_ = v_pre_888_;
goto _start;
}
default: 
{
uint8_t v___x_890_; 
v___x_890_ = 1;
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_891_);
lean_dec(v_x_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_909_, lean_object* v_prec_910_){
_start:
{
switch(lean_obj_tag(v_n_909_))
{
case 0:
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_911_;
}
case 1:
{
lean_object* v_pre_912_; lean_object* v_str_913_; uint8_t v___x_914_; 
v_pre_912_ = lean_ctor_get(v_n_909_, 0);
v_str_913_ = lean_ctor_get(v_n_909_, 1);
v___x_914_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_912_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = 1;
v___x_916_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_917_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_909_, v___x_915_);
v___x_918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc_ref(v_str_913_);
lean_inc(v_pre_912_);
lean_dec_ref_known(v_n_909_, 2);
v___x_920_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_921_ = lean_unsigned_to_nat(1024u);
v___x_922_ = l_Lean_Name_reprPrec(v_pre_912_, v___x_921_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_920_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_String_quote(v_str_913_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_925_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Repr_addAppParen(v___x_928_, v_prec_910_);
return v___x_929_;
}
}
default: 
{
lean_object* v_pre_930_; lean_object* v_i_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_pre_930_ = lean_ctor_get(v_n_909_, 0);
lean_inc(v_pre_930_);
v_i_931_ = lean_ctor_get(v_n_909_, 1);
lean_inc(v_i_931_);
lean_dec_ref_known(v_n_909_, 2);
v___x_932_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_933_ = lean_unsigned_to_nat(1024u);
v___x_934_ = l_Lean_Name_reprPrec(v_pre_930_, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Nat_reprFast(v_i_931_);
v___x_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_937_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Repr_addAppParen(v___x_940_, v_prec_910_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_942_, lean_object* v_prec_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Name_reprPrec(v_n_942_, v_prec_943_);
lean_dec(v_prec_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 1)
{
lean_object* v_pre_948_; lean_object* v_str_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_pre_948_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_pre_948_);
v_str_949_ = lean_ctor_get(v_x_947_, 1);
lean_inc_ref(v_str_949_);
lean_dec_ref_known(v_x_947_, 2);
v___x_950_ = lean_string_capitalize(v_str_949_);
v___x_951_ = l_Lean_Name_str___override(v_pre_948_, v___x_950_);
return v___x_951_;
}
else
{
return v_x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
switch(lean_obj_tag(v_x_952_))
{
case 0:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_inc(v_x_954_);
return v_x_954_;
}
else
{
return v_x_952_;
}
}
case 1:
{
lean_object* v_pre_955_; lean_object* v_str_956_; uint8_t v___x_957_; 
v_pre_955_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_pre_955_);
v_str_956_ = lean_ctor_get(v_x_952_, 1);
lean_inc_ref(v_str_956_);
v___x_957_ = lean_name_eq(v_x_952_, v_x_953_);
lean_dec_ref_known(v_x_952_, 2);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = l_Lean_Name_replacePrefix(v_pre_955_, v_x_953_, v_x_954_);
v___x_959_ = l_Lean_Name_str___override(v___x_958_, v_str_956_);
return v___x_959_;
}
else
{
lean_dec_ref(v_str_956_);
lean_dec(v_pre_955_);
lean_inc(v_x_954_);
return v_x_954_;
}
}
default: 
{
lean_object* v_pre_960_; lean_object* v_i_961_; uint8_t v___x_962_; 
v_pre_960_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_pre_960_);
v_i_961_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_i_961_);
v___x_962_ = lean_name_eq(v_x_952_, v_x_953_);
lean_dec_ref_known(v_x_952_, 2);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l_Lean_Name_replacePrefix(v_pre_960_, v_x_953_, v_x_954_);
v___x_964_ = l_Lean_Name_num___override(v___x_963_, v_i_961_);
return v___x_964_;
}
else
{
lean_dec(v_i_961_);
lean_dec(v_pre_960_);
lean_inc(v_x_954_);
return v_x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Name_replacePrefix(v_x_965_, v_x_966_, v_x_967_);
lean_dec(v_x_967_);
lean_dec(v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
switch(lean_obj_tag(v_x_970_))
{
case 0:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_x_969_);
return v___x_971_;
}
case 1:
{
if (lean_obj_tag(v_x_969_) == 1)
{
lean_object* v_pre_972_; lean_object* v_str_973_; lean_object* v_pre_974_; lean_object* v_str_975_; uint8_t v___x_976_; 
v_pre_972_ = lean_ctor_get(v_x_970_, 0);
v_str_973_ = lean_ctor_get(v_x_970_, 1);
v_pre_974_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_pre_974_);
v_str_975_ = lean_ctor_get(v_x_969_, 1);
lean_inc_ref(v_str_975_);
lean_dec_ref_known(v_x_969_, 2);
v___x_976_ = lean_string_dec_eq(v_str_975_, v_str_973_);
lean_dec_ref(v_str_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_pre_974_);
v___x_977_ = lean_box(0);
return v___x_977_;
}
else
{
v_x_969_ = v_pre_974_;
v_x_970_ = v_pre_972_;
goto _start;
}
}
else
{
lean_object* v___x_979_; 
lean_dec(v_x_969_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
}
default: 
{
if (lean_obj_tag(v_x_969_) == 2)
{
lean_object* v_pre_980_; lean_object* v_i_981_; lean_object* v_pre_982_; lean_object* v_i_983_; uint8_t v___x_984_; 
v_pre_980_ = lean_ctor_get(v_x_970_, 0);
v_i_981_ = lean_ctor_get(v_x_970_, 1);
v_pre_982_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_pre_982_);
v_i_983_ = lean_ctor_get(v_x_969_, 1);
lean_inc(v_i_983_);
lean_dec_ref_known(v_x_969_, 2);
v___x_984_ = lean_nat_dec_eq(v_i_983_, v_i_981_);
lean_dec(v_i_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec(v_pre_982_);
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
v_x_969_ = v_pre_982_;
v_x_970_ = v_pre_980_;
goto _start;
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v_x_969_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Name_eraseSuffix_x3f(v_x_988_, v_x_989_);
lean_dec(v_x_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_991_, lean_object* v_f_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_Name_hasMacroScopes(v_n_991_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_apply_1(v_f_992_, v_n_991_);
return v___x_994_;
}
else
{
lean_object* v_view_995_; lean_object* v_name_996_; lean_object* v_imported_997_; lean_object* v_ctx_998_; lean_object* v_scopes_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
v_view_995_ = l_Lean_extractMacroScopes(v_n_991_);
v_name_996_ = lean_ctor_get(v_view_995_, 0);
v_imported_997_ = lean_ctor_get(v_view_995_, 1);
v_ctx_998_ = lean_ctor_get(v_view_995_, 2);
v_scopes_999_ = lean_ctor_get(v_view_995_, 3);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_view_995_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1001_ = v_view_995_;
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_scopes_999_);
lean_inc(v_ctx_998_);
lean_inc(v_imported_997_);
lean_inc(v_name_996_);
lean_dec(v_view_995_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_apply_1(v_f_992_, v_name_996_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_imported_997_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ctx_998_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_scopes_999_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_MacroScopesView_review(v___x_1005_);
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 1)
{
lean_object* v_pre_1011_; lean_object* v_str_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_pre_1011_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_pre_1011_);
v_str_1012_ = lean_ctor_get(v_x_1010_, 1);
lean_inc_ref(v_str_1012_);
lean_dec_ref_known(v_x_1010_, 2);
v___x_1013_ = lean_string_append(v_str_1012_, v_suffix_1009_);
lean_dec_ref(v_suffix_1009_);
v___x_1014_ = l_Lean_Name_str___override(v_pre_1011_, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Name_str___override(v_x_1010_, v_suffix_1009_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1016_, lean_object* v_suffix_1017_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lean_Name_hasMacroScopes(v_n_1016_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1017_, v_n_1016_);
return v___x_1019_;
}
else
{
lean_object* v_view_1020_; lean_object* v_name_1021_; lean_object* v_imported_1022_; lean_object* v_ctx_1023_; lean_object* v_scopes_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1033_; 
v_view_1020_ = l_Lean_extractMacroScopes(v_n_1016_);
v_name_1021_ = lean_ctor_get(v_view_1020_, 0);
v_imported_1022_ = lean_ctor_get(v_view_1020_, 1);
v_ctx_1023_ = lean_ctor_get(v_view_1020_, 2);
v_scopes_1024_ = lean_ctor_get(v_view_1020_, 3);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_view_1020_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1026_ = v_view_1020_;
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_scopes_1024_);
lean_inc(v_ctx_1023_);
lean_inc(v_imported_1022_);
lean_inc(v_name_1021_);
lean_dec(v_view_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1017_, v_name_1021_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_imported_1022_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_ctx_1023_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_scopes_1024_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_MacroScopesView_review(v___x_1030_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 1)
{
lean_object* v_pre_1036_; lean_object* v_str_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_pre_1036_ = lean_ctor_get(v_x_1035_, 0);
lean_inc(v_pre_1036_);
v_str_1037_ = lean_ctor_get(v_x_1035_, 1);
lean_inc_ref(v_str_1037_);
lean_dec_ref_known(v_x_1035_, 2);
v___x_1038_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1039_ = lean_string_append(v_str_1037_, v___x_1038_);
v___x_1040_ = l_Nat_reprFast(v_idx_1034_);
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = l_Lean_Name_str___override(v_pre_1036_, v___x_1041_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1044_ = l_Nat_reprFast(v_idx_1034_);
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_Name_str___override(v_x_1035_, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1047_, lean_object* v_idx_1048_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = l_Lean_Name_hasMacroScopes(v_n_1047_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1048_, v_n_1047_);
return v___x_1050_;
}
else
{
lean_object* v_view_1051_; lean_object* v_name_1052_; lean_object* v_imported_1053_; lean_object* v_ctx_1054_; lean_object* v_scopes_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_view_1051_ = l_Lean_extractMacroScopes(v_n_1047_);
v_name_1052_ = lean_ctor_get(v_view_1051_, 0);
v_imported_1053_ = lean_ctor_get(v_view_1051_, 1);
v_ctx_1054_ = lean_ctor_get(v_view_1051_, 2);
v_scopes_1055_ = lean_ctor_get(v_view_1051_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_view_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v_view_1051_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_scopes_1055_);
lean_inc(v_ctx_1054_);
lean_inc(v_imported_1053_);
lean_inc(v_name_1052_);
lean_dec(v_view_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1048_, v_name_1052_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_imported_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_ctx_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_scopes_1055_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_MacroScopesView_review(v___x_1061_);
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1065_, lean_object* v_x_1066_){
_start:
{
switch(lean_obj_tag(v_x_1066_))
{
case 0:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Name_str___override(v_x_1066_, v_pre_1065_);
return v___x_1067_;
}
case 1:
{
lean_object* v_pre_1068_; lean_object* v_str_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_pre_1068_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_pre_1068_);
v_str_1069_ = lean_ctor_get(v_x_1066_, 1);
lean_inc_ref(v_str_1069_);
lean_dec_ref_known(v_x_1066_, 2);
v___x_1070_ = lean_string_append(v_pre_1065_, v_str_1069_);
lean_dec_ref(v_str_1069_);
v___x_1071_ = l_Lean_Name_str___override(v_pre_1068_, v___x_1070_);
return v___x_1071_;
}
default: 
{
lean_object* v_pre_1072_; lean_object* v_i_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_pre_1072_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_pre_1072_);
v_i_1073_ = lean_ctor_get(v_x_1066_, 1);
lean_inc(v_i_1073_);
lean_dec_ref_known(v_x_1066_, 2);
v___x_1074_ = l_Lean_Name_str___override(v_pre_1072_, v_pre_1065_);
v___x_1075_ = l_Lean_Name_num___override(v___x_1074_, v_i_1073_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_append_before(lean_object* v_n_1076_, lean_object* v_pre_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = l_Lean_Name_hasMacroScopes(v_n_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Name_appendBefore___lam__0(v_pre_1077_, v_n_1076_);
return v___x_1079_;
}
else
{
lean_object* v_view_1080_; lean_object* v_name_1081_; lean_object* v_imported_1082_; lean_object* v_ctx_1083_; lean_object* v_scopes_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_view_1080_ = l_Lean_extractMacroScopes(v_n_1076_);
v_name_1081_ = lean_ctor_get(v_view_1080_, 0);
v_imported_1082_ = lean_ctor_get(v_view_1080_, 1);
v_ctx_1083_ = lean_ctor_get(v_view_1080_, 2);
v_scopes_1084_ = lean_ctor_get(v_view_1080_, 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_view_1080_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v_view_1080_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_scopes_1084_);
lean_inc(v_ctx_1083_);
lean_inc(v_imported_1082_);
lean_inc(v_name_1081_);
lean_dec(v_view_1080_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = l_Lean_Name_appendBefore___lam__0(v_pre_1077_, v_name_1081_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_imported_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_ctx_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_scopes_1084_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_MacroScopesView_review(v___x_1090_);
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_h__1_1096_, lean_object* v_h__2_1097_, lean_object* v_h__3_1098_, lean_object* v_h__4_1099_){
_start:
{
switch(lean_obj_tag(v_x_1094_))
{
case 0:
{
lean_dec(v_h__3_1098_);
lean_dec(v_h__2_1097_);
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__4_1099_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_apply_1(v_h__1_1096_, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_h__1_1096_);
v___x_1102_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1102_;
}
}
case 1:
{
lean_dec(v_h__3_1098_);
lean_dec(v_h__1_1096_);
if (lean_obj_tag(v_x_1095_) == 1)
{
lean_object* v_pre_1103_; lean_object* v_str_1104_; lean_object* v_pre_1105_; lean_object* v_str_1106_; lean_object* v___x_1107_; 
lean_dec(v_h__4_1099_);
v_pre_1103_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_pre_1103_);
v_str_1104_ = lean_ctor_get(v_x_1094_, 1);
lean_inc_ref(v_str_1104_);
lean_dec_ref_known(v_x_1094_, 2);
v_pre_1105_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_pre_1105_);
v_str_1106_ = lean_ctor_get(v_x_1095_, 1);
lean_inc_ref(v_str_1106_);
lean_dec_ref_known(v_x_1095_, 2);
v___x_1107_ = lean_apply_4(v_h__2_1097_, v_pre_1103_, v_str_1104_, v_pre_1105_, v_str_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_h__2_1097_);
v___x_1108_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1108_;
}
}
default: 
{
lean_dec(v_h__2_1097_);
lean_dec(v_h__1_1096_);
if (lean_obj_tag(v_x_1095_) == 2)
{
lean_object* v_pre_1109_; lean_object* v_i_1110_; lean_object* v_pre_1111_; lean_object* v_i_1112_; lean_object* v___x_1113_; 
lean_dec(v_h__4_1099_);
v_pre_1109_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_pre_1109_);
v_i_1110_ = lean_ctor_get(v_x_1094_, 1);
lean_inc(v_i_1110_);
lean_dec_ref_known(v_x_1094_, 2);
v_pre_1111_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_pre_1111_);
v_i_1112_ = lean_ctor_get(v_x_1095_, 1);
lean_inc(v_i_1112_);
lean_dec_ref_known(v_x_1095_, 2);
v___x_1113_ = lean_apply_4(v_h__3_1098_, v_pre_1109_, v_i_1110_, v_pre_1111_, v_i_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_h__3_1098_);
v___x_1114_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_h__1_1118_, lean_object* v_h__2_1119_, lean_object* v_h__3_1120_, lean_object* v_h__4_1121_){
_start:
{
switch(lean_obj_tag(v_x_1116_))
{
case 0:
{
lean_dec(v_h__3_1120_);
lean_dec(v_h__2_1119_);
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__4_1121_);
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_apply_1(v_h__1_1118_, v___x_1122_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_h__1_1118_);
v___x_1124_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1124_;
}
}
case 1:
{
lean_dec(v_h__3_1120_);
lean_dec(v_h__1_1118_);
if (lean_obj_tag(v_x_1117_) == 1)
{
lean_object* v_pre_1125_; lean_object* v_str_1126_; lean_object* v_pre_1127_; lean_object* v_str_1128_; lean_object* v___x_1129_; 
lean_dec(v_h__4_1121_);
v_pre_1125_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_pre_1125_);
v_str_1126_ = lean_ctor_get(v_x_1116_, 1);
lean_inc_ref(v_str_1126_);
lean_dec_ref_known(v_x_1116_, 2);
v_pre_1127_ = lean_ctor_get(v_x_1117_, 0);
lean_inc(v_pre_1127_);
v_str_1128_ = lean_ctor_get(v_x_1117_, 1);
lean_inc_ref(v_str_1128_);
lean_dec_ref_known(v_x_1117_, 2);
v___x_1129_ = lean_apply_4(v_h__2_1119_, v_pre_1125_, v_str_1126_, v_pre_1127_, v_str_1128_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_h__2_1119_);
v___x_1130_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1130_;
}
}
default: 
{
lean_dec(v_h__2_1119_);
lean_dec(v_h__1_1118_);
if (lean_obj_tag(v_x_1117_) == 2)
{
lean_object* v_pre_1131_; lean_object* v_i_1132_; lean_object* v_pre_1133_; lean_object* v_i_1134_; lean_object* v___x_1135_; 
lean_dec(v_h__4_1121_);
v_pre_1131_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_pre_1131_);
v_i_1132_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_i_1132_);
lean_dec_ref_known(v_x_1116_, 2);
v_pre_1133_ = lean_ctor_get(v_x_1117_, 0);
lean_inc(v_pre_1133_);
v_i_1134_ = lean_ctor_get(v_x_1117_, 1);
lean_inc(v_i_1134_);
lean_dec_ref_known(v_x_1117_, 2);
v___x_1135_ = lean_apply_4(v_h__3_1120_, v_pre_1131_, v_i_1132_, v_pre_1133_, v_i_1134_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
lean_dec(v_h__3_1120_);
v___x_1136_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1137_, lean_object* v_b_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_name_eq(v_a_1137_, v_b_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_Name_instDecidableEq(v_a_1140_, v_b_1141_);
lean_dec(v_b_1141_);
lean_dec(v_a_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1144_){
_start:
{
lean_object* v_namePrefix_1145_; lean_object* v_idx_1146_; lean_object* v___x_1147_; 
v_namePrefix_1145_ = lean_ctor_get(v_g_1144_, 0);
lean_inc(v_namePrefix_1145_);
v_idx_1146_ = lean_ctor_get(v_g_1144_, 1);
lean_inc(v_idx_1146_);
lean_dec_ref(v_g_1144_);
v___x_1147_ = l_Lean_Name_num___override(v_namePrefix_1145_, v_idx_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1148_){
_start:
{
lean_object* v_namePrefix_1149_; lean_object* v_idx_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1159_; 
v_namePrefix_1149_ = lean_ctor_get(v_g_1148_, 0);
v_idx_1150_ = lean_ctor_get(v_g_1148_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_g_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1152_ = v_g_1148_;
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_idx_1150_);
lean_inc(v_namePrefix_1149_);
lean_dec(v_g_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_add(v_idx_1150_, v___x_1154_);
lean_dec(v_idx_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_namePrefix_1149_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1160_){
_start:
{
lean_object* v_namePrefix_1161_; lean_object* v_idx_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
v_namePrefix_1161_ = lean_ctor_get(v_g_1160_, 0);
v_idx_1162_ = lean_ctor_get(v_g_1160_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_g_1160_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1164_ = v_g_1160_;
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
lean_dec(v_g_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
v___x_1166_ = l_Lean_Name_num___override(v_namePrefix_1161_, v_idx_1162_);
v___x_1167_ = lean_unsigned_to_nat(1u);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1167_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_nat_add(v_idx_1162_, v___x_1167_);
lean_dec(v_idx_1162_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_namePrefix_1161_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1175_, lean_object* v_r_1176_, lean_object* v_____r_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_apply_2(v_toPure_1175_, lean_box(0), v_r_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1179_, lean_object* v_setNGen_1180_, lean_object* v_toBind_1181_, lean_object* v_ngen_1182_){
_start:
{
lean_object* v_namePrefix_1183_; lean_object* v_idx_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1197_; 
v_namePrefix_1183_ = lean_ctor_get(v_ngen_1182_, 0);
v_idx_1184_ = lean_ctor_get(v_ngen_1182_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_ngen_1182_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1186_ = v_ngen_1182_;
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_idx_1184_);
lean_inc(v_namePrefix_1183_);
lean_dec(v_ngen_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_r_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc(v_idx_1184_);
lean_inc(v_namePrefix_1183_);
v_r_1188_ = l_Lean_Name_num___override(v_namePrefix_1183_, v_idx_1184_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1189_, 0, v_toPure_1179_);
lean_closure_set(v___f_1189_, 1, v_r_1188_);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_idx_1184_, v___x_1190_);
lean_dec(v_idx_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1191_);
v___x_1193_ = v___x_1186_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_namePrefix_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_apply_1(v_setNGen_1180_, v___x_1193_);
v___x_1195_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1194_, v___f_1189_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1198_, lean_object* v_inst_1199_){
_start:
{
lean_object* v_toApplicative_1200_; lean_object* v_toBind_1201_; lean_object* v_getNGen_1202_; lean_object* v_setNGen_1203_; lean_object* v_toPure_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; 
v_toApplicative_1200_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc_ref(v_toApplicative_1200_);
v_toBind_1201_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc_n(v_toBind_1201_, 2);
lean_dec_ref(v_inst_1198_);
v_getNGen_1202_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc(v_getNGen_1202_);
v_setNGen_1203_ = lean_ctor_get(v_inst_1199_, 1);
lean_inc(v_setNGen_1203_);
lean_dec_ref(v_inst_1199_);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1200_, 1);
lean_inc(v_toPure_1204_);
lean_dec_ref(v_toApplicative_1200_);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1205_, 0, v_toPure_1204_);
lean_closure_set(v___f_1205_, 1, v_setNGen_1203_);
lean_closure_set(v___f_1205_, 2, v_toBind_1201_);
v___x_1206_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v_getNGen_1202_, v___f_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_mkFreshId___redArg(v_inst_1208_, v_inst_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1211_, lean_object* v_inst_1212_, lean_object* v_ngen_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_apply_1(v_setNGen_1211_, v_ngen_1213_);
v___x_1215_ = lean_apply_2(v_inst_1212_, lean_box(0), v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v_getNGen_1218_; lean_object* v_setNGen_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
v_getNGen_1218_ = lean_ctor_get(v_inst_1217_, 0);
v_setNGen_1219_ = lean_ctor_get(v_inst_1217_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_inst_1217_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1221_ = v_inst_1217_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_setNGen_1219_);
lean_inc(v_getNGen_1218_);
lean_dec(v_inst_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_inc(v_inst_1216_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1223_, 0, v_setNGen_1219_);
lean_closure_set(v___f_1223_, 1, v_inst_1216_);
v___x_1224_ = lean_apply_2(v_inst_1216_, lean_box(0), v_getNGen_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___f_1223_);
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___f_1223_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1229_, lean_object* v_n_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1231_, v_inst_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
lean_dec(v_x_1234_);
return v_x_1235_;
}
else
{
lean_object* v_head_1237_; lean_object* v_tail_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v_head_1237_ = lean_ctor_get(v_x_1236_, 0);
v_tail_1238_ = lean_ctor_get(v_x_1236_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1236_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1240_ = v_x_1236_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_tail_1238_);
lean_inc(v_head_1237_);
lean_dec(v_x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
lean_inc(v_x_1234_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 5);
lean_ctor_set(v___x_1240_, 1, v_x_1234_);
lean_ctor_set(v___x_1240_, 0, v_x_1235_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_x_1235_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_x_1234_);
v___x_1243_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l_String_quote(v_head_1237_);
v___x_1245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1243_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v_x_1235_ = v___x_1246_;
v_x_1236_ = v_tail_1238_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_dec(v_x_1250_);
return v_x_1251_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1265_; 
v_head_1253_ = lean_ctor_get(v_x_1252_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1252_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1256_ = v_x_1252_;
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_head_1253_);
lean_dec(v_x_1252_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
lean_inc(v_x_1250_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 5);
lean_ctor_set(v___x_1256_, 1, v_x_1250_);
lean_ctor_set(v___x_1256_, 0, v_x_1251_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_x_1251_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_x_1250_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = l_String_quote(v_head_1253_);
v___x_1261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1250_, v___x_1262_, v_tail_1254_);
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_String_quote(v___y_1266_);
v___x_1268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
lean_object* v___x_1271_; 
lean_dec(v_x_1270_);
v___x_1271_ = lean_box(0);
return v___x_1271_;
}
else
{
lean_object* v_tail_1272_; 
v_tail_1272_ = lean_ctor_get(v_x_1269_, 1);
if (lean_obj_tag(v_tail_1272_) == 0)
{
lean_object* v_head_1273_; lean_object* v___x_1274_; 
lean_dec(v_x_1270_);
v_head_1273_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_head_1273_);
lean_dec_ref_known(v_x_1269_, 2);
v___x_1274_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1273_);
return v___x_1274_;
}
else
{
lean_object* v_head_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v_tail_1272_);
v_head_1275_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_head_1275_);
lean_dec_ref_known(v_x_1269_, 2);
v___x_1276_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1275_);
v___x_1277_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1270_, v___x_1276_, v_tail_1272_);
return v___x_1277_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1290_ = lean_string_length(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1292_ = lean_nat_to_int(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1297_){
_start:
{
if (lean_obj_tag(v_a_1297_) == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1299_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1300_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1297_, v___x_1299_);
v___x_1301_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1302_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1300_);
v___x_1304_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1301_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Std_Format_fill(v___x_1306_);
return v___x_1307_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_unsigned_to_nat(2u);
v___x_1315_ = lean_nat_to_int(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_to_int(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1324_, lean_object* v_prec_1325_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
lean_object* v_ns_1326_; lean_object* v___y_1328_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_ns_1326_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_ns_1326_);
lean_dec_ref_known(v_x_1324_, 1);
v___x_1337_ = lean_unsigned_to_nat(1024u);
v___x_1338_ = lean_nat_dec_le(v___x_1337_, v_prec_1325_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1328_ = v___x_1339_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1328_ = v___x_1340_;
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1329_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1330_ = lean_unsigned_to_nat(1024u);
v___x_1331_ = l_Lean_Name_reprPrec(v_ns_1326_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1329_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_inc(v___y_1328_);
v___x_1333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___y_1328_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = 0;
v___x_1335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*1, v___x_1334_);
v___x_1336_ = l_Repr_addAppParen(v___x_1335_, v_prec_1325_);
return v___x_1336_;
}
}
else
{
lean_object* v_n_1341_; lean_object* v_fields_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1366_; 
v_n_1341_ = lean_ctor_get(v_x_1324_, 0);
v_fields_1342_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1344_ = v_x_1324_;
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_fields_1342_);
lean_inc(v_n_1341_);
lean_dec(v_x_1324_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___y_1347_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(1024u);
v___x_1363_ = lean_nat_dec_le(v___x_1362_, v_prec_1325_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1347_ = v___x_1364_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1347_ = v___x_1365_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1348_ = lean_box(1);
v___x_1349_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1350_ = lean_unsigned_to_nat(1024u);
v___x_1351_ = l_Lean_Name_reprPrec(v_n_1341_, v___x_1350_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1351_);
lean_ctor_set(v___x_1344_, 0, v___x_1349_);
v___x_1353_ = v___x_1344_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1348_);
v___x_1355_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1342_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_inc(v___y_1347_);
v___x_1357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1347_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = 0;
v___x_1359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*1, v___x_1358_);
v___x_1360_ = l_Repr_addAppParen(v___x_1359_, v_prec_1325_);
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1367_, lean_object* v_prec_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1367_, v_prec_1368_);
lean_dec(v_prec_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_nat_to_int(v_a_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1372_, lean_object* v_n_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1375_, lean_object* v_n_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1375_, v_n_1376_);
lean_dec(v_n_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1380_, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_dec(v_x_1383_);
return v_x_1384_;
}
else
{
lean_object* v_head_1386_; lean_object* v_tail_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
v_head_1386_ = lean_ctor_get(v_x_1385_, 0);
v_tail_1387_ = lean_ctor_get(v_x_1385_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1389_ = v_x_1385_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_tail_1387_);
lean_inc(v_head_1386_);
lean_dec(v_x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
lean_inc(v_x_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 5);
lean_ctor_set(v___x_1389_, 1, v_x_1383_);
lean_ctor_set(v___x_1389_, 0, v_x_1384_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_x_1384_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_x_1383_);
v___x_1392_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1386_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1392_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v_x_1384_ = v___x_1395_;
v_x_1385_ = v_tail_1387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_dec(v_x_1399_);
return v_x_1400_;
}
else
{
lean_object* v_head_1402_; lean_object* v_tail_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_head_1402_ = lean_ctor_get(v_x_1401_, 0);
v_tail_1403_ = lean_ctor_get(v_x_1401_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v_x_1401_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_tail_1403_);
lean_inc(v_head_1402_);
lean_dec(v_x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
lean_inc(v_x_1399_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 5);
lean_ctor_set(v___x_1405_, 1, v_x_1399_);
lean_ctor_set(v___x_1405_, 0, v_x_1400_);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_x_1400_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_x_1399_);
v___x_1408_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1402_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1408_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1399_, v___x_1411_, v_tail_1403_);
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_x_1416_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
else
{
lean_object* v_tail_1418_; 
v_tail_1418_ = lean_ctor_get(v_x_1415_, 1);
if (lean_obj_tag(v_tail_1418_) == 0)
{
lean_object* v_head_1419_; lean_object* v___x_1420_; 
lean_dec(v_x_1416_);
v_head_1419_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1419_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1420_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1419_);
return v___x_1420_;
}
else
{
lean_object* v_head_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_inc(v_tail_1418_);
v_head_1421_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1421_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1422_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1421_);
v___x_1423_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1416_, v___x_1422_, v_tail_1418_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1424_){
_start:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1426_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1427_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1424_, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1429_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1427_);
v___x_1431_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1428_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = 0;
v___x_1435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*1, v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_dec(v_x_1445_);
return v_x_1446_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_head_1448_ = lean_ctor_get(v_x_1447_, 0);
v_tail_1449_ = lean_ctor_get(v_x_1447_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_x_1447_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_tail_1449_);
lean_inc(v_head_1448_);
lean_dec(v_x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
lean_inc(v_x_1445_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 5);
lean_ctor_set(v___x_1451_, 1, v_x_1445_);
lean_ctor_set(v___x_1451_, 0, v_x_1446_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_x_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_x_1445_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = l_Lean_Syntax_instRepr_repr(v_head_1448_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v_x_1446_ = v___x_1457_;
v_x_1447_ = v_tail_1449_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
lean_dec(v_x_1461_);
return v_x_1462_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1476_; 
v_head_1464_ = lean_ctor_get(v_x_1463_, 0);
v_tail_1465_ = lean_ctor_get(v_x_1463_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1467_ = v_x_1463_;
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_head_1464_);
lean_dec(v_x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
lean_inc(v_x_1461_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 5);
lean_ctor_set(v___x_1467_, 1, v_x_1461_);
lean_ctor_set(v___x_1467_, 0, v_x_1462_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_x_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_x_1461_);
v___x_1470_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Lean_Syntax_instRepr_repr(v_head_1464_, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1470_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1461_, v___x_1473_, v_tail_1465_);
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_object* v___x_1479_; 
lean_dec(v_x_1478_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
else
{
lean_object* v_tail_1480_; 
v_tail_1480_ = lean_ctor_get(v_x_1477_, 1);
if (lean_obj_tag(v_tail_1480_) == 0)
{
lean_object* v_head_1481_; lean_object* v___x_1482_; 
lean_dec(v_x_1478_);
v_head_1481_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_head_1481_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1482_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1481_);
return v___x_1482_;
}
else
{
lean_object* v_head_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc(v_tail_1480_);
v_head_1483_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_head_1483_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1484_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1483_);
v___x_1485_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1478_, v___x_1484_, v_tail_1480_);
return v___x_1485_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1488_ = lean_string_length(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1490_ = lean_nat_to_int(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = lean_array_get_size(v_xs_1496_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_nat_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1500_ = lean_array_to_list(v_xs_1496_);
v___x_1501_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1502_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1504_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1502_);
v___x_1506_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Std_Format_fill(v___x_1508_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; 
lean_dec_ref(v_xs_1496_);
v___x_1510_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1524_, lean_object* v_prec_1525_){
_start:
{
lean_object* v___y_1527_; 
switch(lean_obj_tag(v_x_1524_))
{
case 0:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(1024u);
v___x_1534_ = lean_nat_dec_le(v___x_1533_, v_prec_1525_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1527_ = v___x_1535_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1527_ = v___x_1536_;
goto v___jp_1526_;
}
}
case 1:
{
lean_object* v_info_1537_; lean_object* v_kind_1538_; lean_object* v_args_1539_; lean_object* v___y_1541_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_info_1537_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_info_1537_);
v_kind_1538_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_kind_1538_);
v_args_1539_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_args_1539_);
lean_dec_ref_known(v_x_1524_, 3);
v___x_1557_ = lean_unsigned_to_nat(1024u);
v___x_1558_ = lean_nat_dec_le(v___x_1557_, v_prec_1525_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1541_ = v___x_1559_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1541_ = v___x_1560_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1542_ = lean_box(1);
v___x_1543_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1544_ = lean_unsigned_to_nat(1024u);
v___x_1545_ = l_instReprSourceInfo_repr(v_info_1537_, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1543_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1542_);
v___x_1548_ = l_Lean_Name_reprPrec(v_kind_1538_, v___x_1544_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1542_);
v___x_1551_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1539_);
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc(v___y_1541_);
v___x_1553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1541_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = 0;
v___x_1555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*1, v___x_1554_);
v___x_1556_ = l_Repr_addAppParen(v___x_1555_, v_prec_1525_);
return v___x_1556_;
}
}
case 2:
{
lean_object* v_info_1561_; lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1587_; 
v_info_1561_ = lean_ctor_get(v_x_1524_, 0);
v_val_1562_ = lean_ctor_get(v_x_1524_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1524_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1564_ = v_x_1524_;
v_isShared_1565_ = v_isSharedCheck_1587_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_inc(v_info_1561_);
lean_dec(v_x_1524_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1587_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___y_1567_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_unsigned_to_nat(1024u);
v___x_1584_ = lean_nat_dec_le(v___x_1583_, v_prec_1525_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1567_ = v___x_1585_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1567_ = v___x_1586_;
goto v___jp_1566_;
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1568_ = lean_box(1);
v___x_1569_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1570_ = lean_unsigned_to_nat(1024u);
v___x_1571_ = l_instReprSourceInfo_repr(v_info_1561_, v___x_1570_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 5);
lean_ctor_set(v___x_1564_, 1, v___x_1571_);
lean_ctor_set(v___x_1564_, 0, v___x_1569_);
v___x_1573_ = v___x_1564_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___x_1568_);
v___x_1575_ = l_String_quote(v_val_1562_);
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1574_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc(v___y_1567_);
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1567_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
v___x_1581_ = l_Repr_addAppParen(v___x_1580_, v_prec_1525_);
return v___x_1581_;
}
}
}
}
default: 
{
lean_object* v_info_1588_; lean_object* v_rawVal_1589_; lean_object* v_val_1590_; lean_object* v_preresolved_1591_; lean_object* v___y_1593_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_info_1588_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_info_1588_);
v_rawVal_1589_ = lean_ctor_get(v_x_1524_, 1);
lean_inc_ref(v_rawVal_1589_);
v_val_1590_ = lean_ctor_get(v_x_1524_, 2);
lean_inc(v_val_1590_);
v_preresolved_1591_ = lean_ctor_get(v_x_1524_, 3);
lean_inc(v_preresolved_1591_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1616_ = lean_unsigned_to_nat(1024u);
v___x_1617_ = lean_nat_dec_le(v___x_1616_, v_prec_1525_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1593_ = v___x_1618_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1593_ = v___x_1619_;
goto v___jp_1592_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1594_ = lean_box(1);
v___x_1595_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1596_ = lean_unsigned_to_nat(1024u);
v___x_1597_ = l_instReprSourceInfo_repr(v_info_1588_, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1595_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___x_1594_);
v___x_1600_ = lean_substring_tostring(v_rawVal_1589_);
v___x_1601_ = l_String_quote(v___x_1600_);
v___x_1602_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1599_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1594_);
v___x_1607_ = l_Lean_Name_reprPrec(v_val_1590_, v___x_1596_);
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___x_1594_);
v___x_1610_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1591_);
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc(v___y_1593_);
v___x_1612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1593_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = 0;
v___x_1614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*1, v___x_1613_);
v___x_1615_ = l_Repr_addAppParen(v___x_1614_, v_prec_1525_);
return v___x_1615_;
}
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1527_);
v___x_1529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___y_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = 0;
v___x_1531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*1, v___x_1530_);
v___x_1532_ = l_Repr_addAppParen(v___x_1531_, v_prec_1525_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = l_Lean_Syntax_instRepr_repr(v___y_1620_, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1623_, lean_object* v_prec_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Syntax_instRepr_repr(v_x_1623_, v_prec_1624_);
lean_dec(v_prec_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1626_, lean_object* v_n_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1629_, lean_object* v_n_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1629_, v_n_1630_);
lean_dec(v_n_1630_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_unsigned_to_nat(7u);
v___x_1648_ = lean_nat_to_int(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1651_ = lean_string_length(v___x_1650_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1653_ = lean_nat_to_int(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1659_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1660_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Lean_Syntax_instRepr_repr(v_x_1658_, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = 0;
v___x_1665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1659_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1668_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1666_);
v___x_1670_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1667_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*1, v___x_1664_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1674_, lean_object* v_x_1675_, lean_object* v_prec_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1678_, lean_object* v_x_1679_, lean_object* v_prec_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1678_, v_x_1679_, v_prec_1680_);
lean_dec(v_prec_1680_);
lean_dec(v_ks_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1683_, 0, v_ks_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1684_){
_start:
{
lean_inc(v_stx_1684_);
return v_stx_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1685_);
lean_dec(v_stx_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1689_; 
v___f_1689_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1692_, lean_object* v_ks_1693_){
_start:
{
lean_object* v___f_1694_; 
v___f_1694_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1695_, lean_object* v_ks_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1695_, v_ks_1696_);
lean_dec(v_ks_1696_);
lean_dec(v_k_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1699_; 
v___f_1699_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1702_, lean_object* v_k_x27_1703_){
_start:
{
lean_object* v___f_1704_; 
v___f_1704_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1705_, lean_object* v_k_x27_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1705_, v_k_x27_1706_);
lean_dec(v_k_x27_1706_);
lean_dec(v_ks_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1708_){
_start:
{
lean_inc(v_s_1708_);
return v_s_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1709_);
lean_dec(v_s_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1713_, lean_object* v_ss_1714_, lean_object* v_n_1715_, lean_object* v_res_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1717_, 0, v_info_1713_);
lean_ctor_set(v___x_1717_, 1, v_ss_1714_);
lean_ctor_set(v___x_1717_, 2, v_n_1715_);
lean_ctor_set(v___x_1717_, 3, v_res_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1727_; 
v___f_1727_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1730_){
_start:
{
lean_object* v___f_1731_; 
v___f_1731_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1732_);
lean_dec(v_k_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1735_, 0, v_k_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
if (lean_obj_tag(v_x_1737_) == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = 1;
return v___x_1738_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
return v___x_1739_;
}
}
else
{
if (lean_obj_tag(v_x_1737_) == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = 0;
return v___x_1740_;
}
else
{
lean_object* v_head_1741_; lean_object* v_tail_1742_; lean_object* v_head_1743_; lean_object* v_tail_1744_; uint8_t v___x_1745_; 
v_head_1741_ = lean_ctor_get(v_x_1736_, 0);
v_tail_1742_ = lean_ctor_get(v_x_1736_, 1);
v_head_1743_ = lean_ctor_get(v_x_1737_, 0);
v_tail_1744_ = lean_ctor_get(v_x_1737_, 1);
v___x_1745_ = lean_string_dec_eq(v_head_1741_, v_head_1743_);
if (v___x_1745_ == 0)
{
return v___x_1745_;
}
else
{
v_x_1736_ = v_tail_1742_;
v_x_1737_ = v_tail_1744_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_res_1749_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1747_, v_x_1748_);
lean_dec(v_x_1748_);
lean_dec(v_x_1747_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v_ns_1753_; lean_object* v_ns_1754_; uint8_t v___x_1755_; 
v_ns_1753_ = lean_ctor_get(v_x_1751_, 0);
v_ns_1754_ = lean_ctor_get(v_x_1752_, 0);
v___x_1755_ = lean_name_eq(v_ns_1753_, v_ns_1754_);
return v___x_1755_;
}
else
{
uint8_t v___x_1756_; 
v___x_1756_ = 0;
return v___x_1756_;
}
}
else
{
if (lean_obj_tag(v_x_1752_) == 1)
{
lean_object* v_n_1757_; lean_object* v_fields_1758_; lean_object* v_n_1759_; lean_object* v_fields_1760_; uint8_t v___x_1761_; 
v_n_1757_ = lean_ctor_get(v_x_1751_, 0);
v_fields_1758_ = lean_ctor_get(v_x_1751_, 1);
v_n_1759_ = lean_ctor_get(v_x_1752_, 0);
v_fields_1760_ = lean_ctor_get(v_x_1752_, 1);
v___x_1761_ = lean_name_eq(v_n_1757_, v_n_1759_);
if (v___x_1761_ == 0)
{
return v___x_1761_;
}
else
{
uint8_t v___x_1762_; 
v___x_1762_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1758_, v_fields_1760_);
return v___x_1762_;
}
}
else
{
uint8_t v___x_1763_; 
v___x_1763_ = 0;
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
uint8_t v_res_1766_; lean_object* v_r_1767_; 
v_res_1766_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1764_, v_x_1765_);
lean_dec_ref(v_x_1765_);
lean_dec_ref(v_x_1764_);
v_r_1767_ = lean_box(v_res_1766_);
return v_r_1767_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
if (lean_obj_tag(v_x_1771_) == 0)
{
uint8_t v___x_1772_; 
v___x_1772_ = 1;
return v___x_1772_;
}
else
{
uint8_t v___x_1773_; 
v___x_1773_ = 0;
return v___x_1773_;
}
}
else
{
if (lean_obj_tag(v_x_1771_) == 0)
{
uint8_t v___x_1774_; 
v___x_1774_ = 0;
return v___x_1774_;
}
else
{
lean_object* v_head_1775_; lean_object* v_tail_1776_; lean_object* v_head_1777_; lean_object* v_tail_1778_; uint8_t v___x_1779_; 
v_head_1775_ = lean_ctor_get(v_x_1770_, 0);
v_tail_1776_ = lean_ctor_get(v_x_1770_, 1);
v_head_1777_ = lean_ctor_get(v_x_1771_, 0);
v_tail_1778_ = lean_ctor_get(v_x_1771_, 1);
v___x_1779_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1775_, v_head_1777_);
if (v___x_1779_ == 0)
{
return v___x_1779_;
}
else
{
v_x_1770_ = v_tail_1776_;
v_x_1771_ = v_tail_1778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1781_, v_x_1782_);
lean_dec(v_x_1782_);
lean_dec(v_x_1781_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
switch(lean_obj_tag(v_x_1785_))
{
case 0:
{
if (lean_obj_tag(v_x_1786_) == 0)
{
uint8_t v___x_1787_; 
v___x_1787_ = 1;
return v___x_1787_;
}
else
{
uint8_t v___x_1788_; 
v___x_1788_ = 0;
return v___x_1788_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1786_) == 1)
{
lean_object* v_kind_1789_; lean_object* v_args_1790_; lean_object* v_kind_1791_; lean_object* v_args_1792_; uint8_t v___x_1793_; 
v_kind_1789_ = lean_ctor_get(v_x_1785_, 1);
v_args_1790_ = lean_ctor_get(v_x_1785_, 2);
v_kind_1791_ = lean_ctor_get(v_x_1786_, 1);
v_args_1792_ = lean_ctor_get(v_x_1786_, 2);
v___x_1793_ = lean_name_eq(v_kind_1789_, v_kind_1791_);
if (v___x_1793_ == 0)
{
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = lean_array_get_size(v_args_1790_);
v___x_1795_ = lean_array_get_size(v_args_1792_);
v___x_1796_ = lean_nat_dec_eq(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
return v___x_1796_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1790_, v_args_1792_, v___x_1794_);
return v___x_1797_;
}
}
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = 0;
return v___x_1798_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1786_) == 2)
{
lean_object* v_val_1799_; lean_object* v_val_1800_; uint8_t v___x_1801_; 
v_val_1799_ = lean_ctor_get(v_x_1785_, 1);
v_val_1800_ = lean_ctor_get(v_x_1786_, 1);
v___x_1801_ = lean_string_dec_eq(v_val_1799_, v_val_1800_);
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
default: 
{
if (lean_obj_tag(v_x_1786_) == 3)
{
lean_object* v_rawVal_1803_; lean_object* v_val_1804_; lean_object* v_preresolved_1805_; lean_object* v_rawVal_1806_; lean_object* v_val_1807_; lean_object* v_preresolved_1808_; uint8_t v___y_1810_; uint8_t v___x_1812_; 
v_rawVal_1803_ = lean_ctor_get(v_x_1785_, 1);
v_val_1804_ = lean_ctor_get(v_x_1785_, 2);
v_preresolved_1805_ = lean_ctor_get(v_x_1785_, 3);
v_rawVal_1806_ = lean_ctor_get(v_x_1786_, 1);
v_val_1807_ = lean_ctor_get(v_x_1786_, 2);
v_preresolved_1808_ = lean_ctor_get(v_x_1786_, 3);
lean_inc_ref(v_rawVal_1806_);
lean_inc_ref(v_rawVal_1803_);
v___x_1812_ = lean_substring_beq(v_rawVal_1803_, v_rawVal_1806_);
if (v___x_1812_ == 0)
{
v___y_1810_ = v___x_1812_;
goto v___jp_1809_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_name_eq(v_val_1804_, v_val_1807_);
v___y_1810_ = v___x_1813_;
goto v___jp_1809_;
}
v___jp_1809_:
{
if (v___y_1810_ == 0)
{
return v___y_1810_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1805_, v_preresolved_1808_);
return v___x_1811_;
}
}
}
else
{
uint8_t v___x_1814_; 
v___x_1814_ = 0;
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1815_, lean_object* v_ys_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v_zero_1818_; uint8_t v_isZero_1819_; 
v_zero_1818_ = lean_unsigned_to_nat(0u);
v_isZero_1819_ = lean_nat_dec_eq(v_x_1817_, v_zero_1818_);
if (v_isZero_1819_ == 1)
{
lean_dec(v_x_1817_);
return v_isZero_1819_;
}
else
{
lean_object* v_one_1820_; lean_object* v_n_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_one_1820_ = lean_unsigned_to_nat(1u);
v_n_1821_ = lean_nat_sub(v_x_1817_, v_one_1820_);
lean_dec(v_x_1817_);
v___x_1822_ = lean_array_fget_borrowed(v_xs_1815_, v_n_1821_);
v___x_1823_ = lean_array_fget_borrowed(v_ys_1816_, v_n_1821_);
v___x_1824_ = l_Lean_Syntax_structEq(v___x_1822_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_dec(v_n_1821_);
return v___x_1824_;
}
else
{
v_x_1817_ = v_n_1821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1826_, lean_object* v_ys_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v_res_1829_; lean_object* v_r_1830_; 
v_res_1829_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1826_, v_ys_1827_, v_x_1828_);
lean_dec_ref(v_ys_1827_);
lean_dec_ref(v_xs_1826_);
v_r_1830_ = lean_box(v_res_1829_);
return v_r_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Lean_Syntax_structEq(v_x_1831_, v_x_1832_);
lean_dec(v_x_1832_);
lean_dec(v_x_1831_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1835_, lean_object* v_ys_1836_, lean_object* v_hsz_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1835_, v_ys_1836_, v_x_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1841_, lean_object* v_ys_1842_, lean_object* v_hsz_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_res_1846_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1841_, v_ys_1842_, v_hsz_1843_, v_x_1844_, v_x_1845_);
lean_dec_ref(v_ys_1842_);
lean_dec_ref(v_xs_1841_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1852_; 
v___f_1852_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1855_){
_start:
{
lean_object* v___f_1856_; 
v___f_1856_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Syntax_instBEqTSyntax(v_k_1857_);
lean_dec(v_k_1857_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1859_, lean_object* v_i_1860_){
_start:
{
lean_object* v_zero_1861_; uint8_t v_isZero_1862_; 
v_zero_1861_ = lean_unsigned_to_nat(0u);
v_isZero_1862_ = lean_nat_dec_eq(v_i_1860_, v_zero_1861_);
if (v_isZero_1862_ == 1)
{
lean_object* v___x_1863_; 
lean_dec(v_i_1860_);
v___x_1863_ = lean_box(0);
return v___x_1863_;
}
else
{
lean_object* v_one_1864_; lean_object* v_n_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_one_1864_ = lean_unsigned_to_nat(1u);
v_n_1865_ = lean_nat_sub(v_i_1860_, v_one_1864_);
lean_dec(v_i_1860_);
v___x_1866_ = lean_array_fget_borrowed(v_as_1859_, v_n_1865_);
v___x_1867_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
v_i_1860_ = v_n_1865_;
goto _start;
}
else
{
lean_dec(v_n_1865_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1869_){
_start:
{
switch(lean_obj_tag(v_x_1869_))
{
case 2:
{
lean_object* v_info_1870_; lean_object* v___x_1871_; 
v_info_1870_ = lean_ctor_get(v_x_1869_, 0);
lean_inc(v_info_1870_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_info_1870_);
return v___x_1871_;
}
case 3:
{
lean_object* v_info_1872_; lean_object* v___x_1873_; 
v_info_1872_ = lean_ctor_get(v_x_1869_, 0);
lean_inc(v_info_1872_);
v___x_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_info_1872_);
return v___x_1873_;
}
case 1:
{
lean_object* v_info_1874_; 
v_info_1874_ = lean_ctor_get(v_x_1869_, 0);
if (lean_obj_tag(v_info_1874_) == 2)
{
lean_object* v_args_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_args_1875_ = lean_ctor_get(v_x_1869_, 2);
v___x_1876_ = lean_array_get_size(v_args_1875_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1875_, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; 
lean_inc(v_info_1874_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_info_1874_);
return v___x_1878_;
}
}
default: 
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1880_);
lean_dec(v_x_1880_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1882_, lean_object* v_i_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1882_, v_i_1883_);
lean_dec_ref(v_as_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1885_, lean_object* v_i_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1885_, v_i_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1889_, lean_object* v_i_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1889_, v_i_1890_, v_a_1891_);
lean_dec_ref(v_as_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_box(2);
return v___x_1895_;
}
else
{
lean_object* v_val_1896_; 
v_val_1896_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v___x_1894_, 1);
return v_val_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Syntax_getTailInfo(v_stx_1897_);
lean_dec(v_stx_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1899_);
if (lean_obj_tag(v___x_1900_) == 1)
{
lean_object* v_val_1901_; 
v_val_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v___x_1900_, 1);
if (lean_obj_tag(v_val_1901_) == 0)
{
lean_object* v_trailing_1902_; lean_object* v_startPos_1903_; lean_object* v_stopPos_1904_; lean_object* v___x_1905_; 
v_trailing_1902_ = lean_ctor_get(v_val_1901_, 2);
lean_inc_ref(v_trailing_1902_);
lean_dec_ref_known(v_val_1901_, 4);
v_startPos_1903_ = lean_ctor_get(v_trailing_1902_, 1);
lean_inc(v_startPos_1903_);
v_stopPos_1904_ = lean_ctor_get(v_trailing_1902_, 2);
lean_inc(v_stopPos_1904_);
lean_dec_ref(v_trailing_1902_);
v___x_1905_ = lean_nat_sub(v_stopPos_1904_, v_startPos_1903_);
lean_dec(v_startPos_1903_);
lean_dec(v_stopPos_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; 
lean_dec(v_val_1901_);
v___x_1906_ = lean_unsigned_to_nat(0u);
return v___x_1906_;
}
}
else
{
lean_object* v___x_1907_; 
lean_dec(v___x_1900_);
v___x_1907_ = lean_unsigned_to_nat(0u);
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Syntax_getTrailingSize(v_stx_1908_);
lean_dec(v_stx_1908_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = l_Lean_Syntax_getTailInfo(v_stx_1910_);
v___x_1912_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1911_);
lean_dec(v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1913_);
lean_dec(v_stx_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1915_, uint8_t v_canonicalOnly_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = l_Lean_Syntax_getTailInfo(v_stx_1915_);
v___x_1918_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1917_, v_canonicalOnly_1916_);
lean_dec(v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1919_, lean_object* v_canonicalOnly_1920_){
_start:
{
uint8_t v_canonicalOnly_boxed_1921_; lean_object* v_res_1922_; 
v_canonicalOnly_boxed_1921_ = lean_unbox(v_canonicalOnly_1920_);
v_res_1922_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1919_, v_canonicalOnly_boxed_1921_);
lean_dec(v_stx_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1923_, uint8_t v_withLeading_1924_, uint8_t v_withTrailing_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Syntax_getHeadInfo(v_stx_1923_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_leading_1927_; lean_object* v_pos_1928_; lean_object* v___x_1929_; 
v_leading_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_ref(v_leading_1927_);
v_pos_1928_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_pos_1928_);
lean_dec_ref_known(v___x_1926_, 4);
v___x_1929_ = l_Lean_Syntax_getTailInfo(v_stx_1923_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_trailing_1930_; lean_object* v_endPos_1931_; lean_object* v_str_1932_; lean_object* v_startPos_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1947_; 
v_trailing_1930_ = lean_ctor_get(v___x_1929_, 2);
lean_inc_ref(v_trailing_1930_);
v_endPos_1931_ = lean_ctor_get(v___x_1929_, 3);
lean_inc(v_endPos_1931_);
lean_dec_ref_known(v___x_1929_, 4);
v_str_1932_ = lean_ctor_get(v_leading_1927_, 0);
v_startPos_1933_ = lean_ctor_get(v_leading_1927_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_leading_1927_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v_leading_1927_, 2);
lean_dec(v_unused_1948_);
v___x_1935_ = v_leading_1927_;
v_isShared_1936_ = v_isSharedCheck_1947_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_startPos_1933_);
lean_inc(v_str_1932_);
lean_dec(v_leading_1927_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1947_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1945_; 
if (v_withLeading_1924_ == 0)
{
lean_dec(v_startPos_1933_);
v___y_1945_ = v_pos_1928_;
goto v___jp_1944_;
}
else
{
lean_dec(v_pos_1928_);
v___y_1945_ = v_startPos_1933_;
goto v___jp_1944_;
}
v___jp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 2, v___y_1939_);
lean_ctor_set(v___x_1935_, 1, v___y_1938_);
v___x_1941_ = v___x_1935_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_str_1932_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___y_1938_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v___y_1939_);
v___x_1941_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
}
v___jp_1944_:
{
if (v_withTrailing_1925_ == 0)
{
lean_dec_ref(v_trailing_1930_);
v___y_1938_ = v___y_1945_;
v___y_1939_ = v_endPos_1931_;
goto v___jp_1937_;
}
else
{
lean_object* v_stopPos_1946_; 
lean_dec(v_endPos_1931_);
v_stopPos_1946_ = lean_ctor_get(v_trailing_1930_, 2);
lean_inc(v_stopPos_1946_);
lean_dec_ref(v_trailing_1930_);
v___y_1938_ = v___y_1945_;
v___y_1939_ = v_stopPos_1946_;
goto v___jp_1937_;
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec(v___x_1929_);
lean_dec(v_pos_1928_);
lean_dec_ref(v_leading_1927_);
v___x_1949_ = lean_box(0);
return v___x_1949_;
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v___x_1926_);
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1951_, lean_object* v_withLeading_1952_, lean_object* v_withTrailing_1953_){
_start:
{
uint8_t v_withLeading_boxed_1954_; uint8_t v_withTrailing_boxed_1955_; lean_object* v_res_1956_; 
v_withLeading_boxed_1954_ = lean_unbox(v_withLeading_1952_);
v_withTrailing_boxed_1955_ = lean_unbox(v_withTrailing_1953_);
v_res_1956_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1951_, v_withLeading_boxed_1954_, v_withTrailing_boxed_1955_);
lean_dec(v_stx_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1957_, lean_object* v_f_1958_, lean_object* v_i_1959_){
_start:
{
lean_object* v_zero_1960_; uint8_t v_isZero_1961_; 
v_zero_1960_ = lean_unsigned_to_nat(0u);
v_isZero_1961_ = lean_nat_dec_eq(v_i_1959_, v_zero_1960_);
if (v_isZero_1961_ == 1)
{
lean_object* v___x_1962_; 
lean_dec(v_i_1959_);
lean_dec_ref(v_f_1958_);
lean_dec_ref(v_a_1957_);
v___x_1962_ = lean_box(0);
return v___x_1962_;
}
else
{
lean_object* v_one_1963_; lean_object* v_n_1964_; lean_object* v_v_1965_; lean_object* v___x_1966_; 
v_one_1963_ = lean_unsigned_to_nat(1u);
v_n_1964_ = lean_nat_sub(v_i_1959_, v_one_1963_);
lean_dec(v_i_1959_);
v_v_1965_ = lean_array_fget_borrowed(v_a_1957_, v_n_1964_);
lean_inc_ref(v_f_1958_);
lean_inc(v_v_1965_);
v___x_1966_ = lean_apply_1(v_f_1958_, v_v_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
v_i_1959_ = v_n_1964_;
goto _start;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_f_1958_);
v_val_1968_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1970_ = v___x_1966_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v___x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_array_fset(v_a_1957_, v_n_1964_, v_val_1968_);
lean_dec(v_n_1964_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1977_, lean_object* v_a_1978_, lean_object* v_f_1979_, lean_object* v_i_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1978_, v_f_1979_, v_i_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1982_, lean_object* v_x_1983_){
_start:
{
switch(lean_obj_tag(v_x_1983_))
{
case 2:
{
lean_object* v_val_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_val_1984_ = lean_ctor_get(v_x_1983_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_x_1983_, 0);
lean_dec(v_unused_1993_);
v___x_1986_ = v_x_1983_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_val_1984_);
lean_dec(v_x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_info_1982_);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_info_1982_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_val_1984_);
v___x_1989_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
return v___x_1990_;
}
}
}
case 3:
{
lean_object* v_rawVal_1994_; lean_object* v_val_1995_; lean_object* v_preresolved_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_rawVal_1994_ = lean_ctor_get(v_x_1983_, 1);
v_val_1995_ = lean_ctor_get(v_x_1983_, 2);
v_preresolved_1996_ = lean_ctor_get(v_x_1983_, 3);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v_x_1983_, 0);
lean_dec(v_unused_2005_);
v___x_1998_ = v_x_1983_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_preresolved_1996_);
lean_inc(v_val_1995_);
lean_inc(v_rawVal_1994_);
lean_dec(v_x_1983_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_info_1982_);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_info_1982_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_rawVal_1994_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_val_1995_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_preresolved_1996_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
}
case 1:
{
lean_object* v_info_2006_; lean_object* v_kind_2007_; lean_object* v_args_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2026_; 
v_info_2006_ = lean_ctor_get(v_x_1983_, 0);
v_kind_2007_ = lean_ctor_get(v_x_1983_, 1);
v_args_2008_ = lean_ctor_get(v_x_1983_, 2);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2010_ = v_x_1983_;
v_isShared_2011_ = v_isSharedCheck_2026_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_args_2008_);
lean_inc(v_kind_2007_);
lean_inc(v_info_2006_);
lean_dec(v_x_1983_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2026_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_array_get_size(v_args_2008_);
v___x_2013_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1982_, v_args_2008_, v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2014_; 
lean_del_object(v___x_2010_);
lean_dec(v_kind_2007_);
lean_dec(v_info_2006_);
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_val_2015_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2017_ = v___x_2013_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 2, v_val_2015_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_info_2006_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_kind_2007_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_val_2015_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2027_; 
lean_dec(v_x_1983_);
lean_dec(v_info_1982_);
v___x_2027_ = lean_box(0);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2028_, lean_object* v_a_2029_, lean_object* v_i_2030_){
_start:
{
lean_object* v_zero_2031_; uint8_t v_isZero_2032_; 
v_zero_2031_ = lean_unsigned_to_nat(0u);
v_isZero_2032_ = lean_nat_dec_eq(v_i_2030_, v_zero_2031_);
if (v_isZero_2032_ == 1)
{
lean_object* v___x_2033_; 
lean_dec(v_i_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_info_2028_);
v___x_2033_ = lean_box(0);
return v___x_2033_;
}
else
{
lean_object* v_one_2034_; lean_object* v_n_2035_; lean_object* v_v_2036_; lean_object* v___x_2037_; 
v_one_2034_ = lean_unsigned_to_nat(1u);
v_n_2035_ = lean_nat_sub(v_i_2030_, v_one_2034_);
lean_dec(v_i_2030_);
v_v_2036_ = lean_array_fget_borrowed(v_a_2029_, v_n_2035_);
lean_inc(v_v_2036_);
lean_inc(v_info_2028_);
v___x_2037_ = l_Lean_Syntax_setTailInfoAux(v_info_2028_, v_v_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
v_i_2030_ = v_n_2035_;
goto _start;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_info_2028_);
v_val_2039_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2041_ = v___x_2037_;
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v___x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_array_fset(v_a_2029_, v_n_2035_, v_val_2039_);
lean_dec(v_n_2035_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2048_, lean_object* v_info_2049_){
_start:
{
lean_object* v___x_2050_; 
lean_inc(v_stx_2048_);
v___x_2050_ = l_Lean_Syntax_setTailInfoAux(v_info_2049_, v_stx_2048_);
if (lean_obj_tag(v___x_2050_) == 0)
{
return v_stx_2048_;
}
else
{
lean_object* v_val_2051_; 
lean_dec(v_stx_2048_);
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2050_, 1);
return v_val_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Syntax_getTailInfo(v_stx_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_trailing_2054_; lean_object* v_leading_2055_; lean_object* v_pos_2056_; lean_object* v_endPos_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2075_; 
v_trailing_2054_ = lean_ctor_get(v___x_2053_, 2);
v_leading_2055_ = lean_ctor_get(v___x_2053_, 0);
v_pos_2056_ = lean_ctor_get(v___x_2053_, 1);
v_endPos_2057_ = lean_ctor_get(v___x_2053_, 3);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2059_ = v___x_2053_;
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_endPos_2057_);
lean_inc(v_trailing_2054_);
lean_inc(v_pos_2056_);
lean_inc(v_leading_2055_);
lean_dec(v___x_2053_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_str_2061_; lean_object* v_startPos_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2073_; 
v_str_2061_ = lean_ctor_get(v_trailing_2054_, 0);
v_startPos_2062_ = lean_ctor_get(v_trailing_2054_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_trailing_2054_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_trailing_2054_, 2);
lean_dec(v_unused_2074_);
v___x_2064_ = v_trailing_2054_;
v_isShared_2065_ = v_isSharedCheck_2073_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_startPos_2062_);
lean_inc(v_str_2061_);
lean_dec(v_trailing_2054_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2073_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
lean_inc(v_startPos_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 2, v_startPos_2062_);
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_str_2061_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_startPos_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_startPos_2062_);
v___x_2067_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 2, v___x_2067_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_leading_2055_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_pos_2056_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_endPos_2057_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Syntax_setTailInfo(v_stx_2052_, v___x_2069_);
return v___x_2070_;
}
}
}
}
}
else
{
lean_dec(v___x_2053_);
return v_stx_2052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2076_, lean_object* v_f_2077_, lean_object* v_i_2078_){
_start:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_array_get_size(v_a_2076_);
v___x_2080_ = lean_nat_dec_lt(v_i_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v_i_2078_);
lean_dec_ref(v_f_2077_);
lean_dec_ref(v_a_2076_);
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v_v_2082_; lean_object* v___x_2083_; 
v_v_2082_ = lean_array_fget_borrowed(v_a_2076_, v_i_2078_);
lean_inc_ref(v_f_2077_);
lean_inc(v_v_2082_);
v___x_2083_ = lean_apply_1(v_f_2077_, v_v_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v_i_2078_, v___x_2084_);
lean_dec(v_i_2078_);
v_i_2078_ = v___x_2085_;
goto _start;
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_f_2077_);
v_val_2087_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2089_ = v___x_2083_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v___x_2083_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_array_fset(v_a_2076_, v_i_2078_, v_val_2087_);
lean_dec(v_i_2078_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2096_, lean_object* v_inst_2097_, lean_object* v_a_2098_, lean_object* v_f_2099_, lean_object* v_i_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2098_, v_f_2099_, v_i_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_inst_2103_, lean_object* v_a_2104_, lean_object* v_f_2105_, lean_object* v_i_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2102_, v_inst_2103_, v_a_2104_, v_f_2105_, v_i_2106_);
lean_dec(v_inst_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2108_, lean_object* v_x_2109_){
_start:
{
switch(lean_obj_tag(v_x_2109_))
{
case 2:
{
lean_object* v_val_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_val_2110_ = lean_ctor_get(v_x_2109_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_x_2109_, 0);
lean_dec(v_unused_2119_);
v___x_2112_ = v_x_2109_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_val_2110_);
lean_dec(v_x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_info_2108_);
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_info_2108_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_val_2110_);
v___x_2115_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
}
case 3:
{
lean_object* v_rawVal_2120_; lean_object* v_val_2121_; lean_object* v_preresolved_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_rawVal_2120_ = lean_ctor_get(v_x_2109_, 1);
v_val_2121_ = lean_ctor_get(v_x_2109_, 2);
v_preresolved_2122_ = lean_ctor_get(v_x_2109_, 3);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_x_2109_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v_x_2109_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_preresolved_2122_);
lean_inc(v_val_2121_);
lean_inc(v_rawVal_2120_);
lean_dec(v_x_2109_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_info_2108_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_info_2108_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_rawVal_2120_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_val_2121_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_preresolved_2122_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
}
case 1:
{
lean_object* v_info_2132_; lean_object* v_kind_2133_; lean_object* v_args_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2152_; 
v_info_2132_ = lean_ctor_get(v_x_2109_, 0);
v_kind_2133_ = lean_ctor_get(v_x_2109_, 1);
v_args_2134_ = lean_ctor_get(v_x_2109_, 2);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2136_ = v_x_2109_;
v_isShared_2137_ = v_isSharedCheck_2152_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_args_2134_);
lean_inc(v_kind_2133_);
lean_inc(v_info_2132_);
lean_dec(v_x_2109_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2152_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2108_, v_args_2134_, v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 1)
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2150_; 
v_val_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 2, v_val_2140_);
v___x_2145_ = v___x_2136_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_info_2132_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_kind_2133_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_val_2140_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v___x_2151_; 
lean_dec(v___x_2139_);
lean_del_object(v___x_2136_);
lean_dec(v_kind_2133_);
lean_dec(v_info_2132_);
v___x_2151_ = lean_box(0);
return v___x_2151_;
}
}
}
default: 
{
lean_object* v___x_2153_; 
lean_dec(v_x_2109_);
lean_dec(v_info_2108_);
v___x_2153_ = lean_box(0);
return v___x_2153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2154_, lean_object* v_a_2155_, lean_object* v_i_2156_){
_start:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_get_size(v_a_2155_);
v___x_2158_ = lean_nat_dec_lt(v_i_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_dec(v_i_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_info_2154_);
v___x_2159_ = lean_box(0);
return v___x_2159_;
}
else
{
lean_object* v_v_2160_; lean_object* v___x_2161_; 
v_v_2160_ = lean_array_fget_borrowed(v_a_2155_, v_i_2156_);
lean_inc(v_v_2160_);
lean_inc(v_info_2154_);
v___x_2161_ = l_Lean_Syntax_setHeadInfoAux(v_info_2154_, v_v_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_nat_add(v_i_2156_, v___x_2162_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2163_;
goto _start;
}
else
{
lean_object* v_val_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_info_2154_);
v_val_2165_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2167_ = v___x_2161_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_val_2165_);
lean_dec(v___x_2161_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_array_fset(v_a_2155_, v_i_2156_, v_val_2165_);
lean_dec(v_i_2156_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2174_, lean_object* v_info_2175_){
_start:
{
lean_object* v___x_2176_; 
lean_inc(v_stx_2174_);
v___x_2176_ = l_Lean_Syntax_setHeadInfoAux(v_info_2175_, v_stx_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
return v_stx_2174_;
}
else
{
lean_object* v_val_2177_; 
lean_dec(v_stx_2174_);
v_val_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_val_2177_);
lean_dec_ref_known(v___x_2176_, 1);
return v_val_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2178_, lean_object* v_x_2179_){
_start:
{
switch(lean_obj_tag(v_x_2179_))
{
case 0:
{
lean_dec(v_info_2178_);
return v_x_2179_;
}
case 1:
{
lean_object* v_kind_2180_; lean_object* v_args_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_kind_2180_ = lean_ctor_get(v_x_2179_, 1);
v_args_2181_ = lean_ctor_get(v_x_2179_, 2);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v_x_2179_, 0);
lean_dec(v_unused_2189_);
v___x_2183_ = v_x_2179_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_args_2181_);
lean_inc(v_kind_2180_);
lean_dec(v_x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v_info_2178_);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_info_2178_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_kind_2180_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_args_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
case 2:
{
lean_object* v_val_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_val_2190_ = lean_ctor_get(v_x_2179_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_x_2179_, 0);
lean_dec(v_unused_2198_);
v___x_2192_ = v_x_2179_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_val_2190_);
lean_dec(v_x_2179_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_info_2178_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_info_2178_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_val_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
default: 
{
lean_object* v_rawVal_2199_; lean_object* v_val_2200_; lean_object* v_preresolved_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_rawVal_2199_ = lean_ctor_get(v_x_2179_, 1);
v_val_2200_ = lean_ctor_get(v_x_2179_, 2);
v_preresolved_2201_ = lean_ctor_get(v_x_2179_, 3);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v_x_2179_, 0);
lean_dec(v_unused_2209_);
v___x_2203_ = v_x_2179_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_preresolved_2201_);
lean_inc(v_val_2200_);
lean_inc(v_rawVal_2199_);
lean_dec(v_x_2179_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_info_2178_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_info_2178_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_rawVal_2199_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_val_2200_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_preresolved_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2213_){
_start:
{
switch(lean_obj_tag(v_x_2213_))
{
case 2:
{
lean_object* v_info_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v_info_2214_ = lean_ctor_get(v_x_2213_, 0);
v___x_2215_ = 0;
v___x_2216_ = l_Lean_SourceInfo_getPos_x3f(v_info_2214_, v___x_2215_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v___x_2217_; 
lean_dec_ref_known(v_x_2213_, 2);
v___x_2217_ = lean_box(0);
return v___x_2217_;
}
else
{
lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v___x_2216_, 0);
lean_dec(v_unused_2225_);
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v_x_2213_);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_x_2213_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
case 3:
{
lean_object* v_info_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; 
v_info_2226_ = lean_ctor_get(v_x_2213_, 0);
v___x_2227_ = 0;
v___x_2228_ = l_Lean_SourceInfo_getPos_x3f(v_info_2226_, v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref_known(v_x_2213_, 4);
v___x_2229_ = lean_box(0);
return v___x_2229_;
}
else
{
lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2228_, 0);
lean_dec(v_unused_2237_);
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_x_2213_);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_x_2213_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
case 1:
{
lean_object* v_info_2238_; 
v_info_2238_ = lean_ctor_get(v_x_2213_, 0);
if (lean_obj_tag(v_info_2238_) == 2)
{
lean_object* v_args_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; lean_object* v_fst_2245_; 
v_args_2239_ = lean_ctor_get(v_x_2213_, 2);
lean_inc_ref(v_args_2239_);
lean_dec_ref_known(v_x_2213_, 3);
v___x_2240_ = lean_box(0);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2242_ = lean_array_size(v_args_2239_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2239_, v_sz_2242_, v___x_2243_, v___x_2241_);
lean_dec_ref(v_args_2239_);
v_fst_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_fst_2245_);
lean_dec_ref(v___x_2244_);
if (lean_obj_tag(v_fst_2245_) == 0)
{
return v___x_2240_;
}
else
{
lean_object* v_val_2246_; 
v_val_2246_ = lean_ctor_get(v_fst_2245_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v_fst_2245_, 1);
return v_val_2246_;
}
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_x_2213_);
return v___x_2247_;
}
}
default: 
{
lean_object* v___x_2248_; 
lean_dec(v_x_2213_);
v___x_2248_ = lean_box(0);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2249_, size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_b_2252_){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
if (v___x_2253_ == 0)
{
lean_inc_ref(v_b_2252_);
return v_b_2252_;
}
else
{
lean_object* v___x_2254_; lean_object* v_a_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_box(0);
v_a_2255_ = lean_array_uget_borrowed(v_as_2249_, v_i_2251_);
lean_inc(v_a_2255_);
v___x_2256_ = l_Lean_Syntax_getHead_x3f(v_a_2255_);
if (lean_obj_tag(v___x_2256_) == 1)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2254_);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; 
lean_dec(v___x_2256_);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2251_, v___x_2260_);
v_i_2251_ = v___x_2261_;
v_b_2252_ = v___x_2259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2263_, lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_b_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2263_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2266_);
lean_dec_ref(v_b_2266_);
lean_dec_ref(v_as_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2270_, lean_object* v_source_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2272_ = l_Lean_Syntax_getHeadInfo(v_source_2271_);
v___x_2273_ = l_Lean_Syntax_setHeadInfo(v_target_2270_, v___x_2272_);
v___x_2274_ = l_Lean_Syntax_getTailInfo(v_source_2271_);
v___x_2275_ = l_Lean_Syntax_setTailInfo(v___x_2273_, v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2276_, lean_object* v_source_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2276_, v_source_2277_);
lean_dec(v_source_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2279_){
_start:
{
uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = 0;
v___x_2281_ = l_Lean_SourceInfo_fromRef(v_stx_2279_, v___x_2280_);
v___x_2282_ = l_Lean_Syntax_setHeadInfo(v_stx_2279_, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2283_, lean_object* v_withRef_2284_, lean_object* v_x_2285_, lean_object* v_oldRef_2286_){
_start:
{
lean_object* v_ref_2287_; lean_object* v___x_2288_; 
v_ref_2287_ = l_Lean_replaceRef(v_val_2283_, v_oldRef_2286_);
v___x_2288_ = lean_apply_3(v_withRef_2284_, lean_box(0), v_ref_2287_, v_x_2285_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2289_, lean_object* v_withRef_2290_, lean_object* v_x_2291_, lean_object* v_oldRef_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2289_, v_withRef_2290_, v_x_2291_, v_oldRef_2292_);
lean_dec(v_oldRef_2292_);
lean_dec(v_val_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2294_, lean_object* v_withRef_2295_, lean_object* v_toBind_2296_, lean_object* v_getRef_2297_, lean_object* v_____do__lift_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_dec(v_getRef_2297_);
lean_dec(v_toBind_2296_);
lean_dec(v_withRef_2295_);
return v_x_2294_;
}
else
{
lean_object* v_val_2300_; lean_object* v___f_2301_; lean_object* v___x_2302_; 
v_val_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2301_, 0, v_val_2300_);
lean_closure_set(v___f_2301_, 1, v_withRef_2295_);
lean_closure_set(v___f_2301_, 2, v_x_2294_);
v___x_2302_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v_getRef_2297_, v___f_2301_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_x_2305_){
_start:
{
lean_object* v_toBind_2306_; lean_object* v_getRef_2307_; lean_object* v_withRef_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; 
v_toBind_2306_ = lean_ctor_get(v_inst_2303_, 1);
lean_inc_n(v_toBind_2306_, 2);
lean_dec_ref(v_inst_2303_);
v_getRef_2307_ = lean_ctor_get(v_inst_2304_, 0);
lean_inc_n(v_getRef_2307_, 2);
v_withRef_2308_ = lean_ctor_get(v_inst_2304_, 1);
lean_inc(v_withRef_2308_);
lean_dec_ref(v_inst_2304_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2309_, 0, v_x_2305_);
lean_closure_set(v___f_2309_, 1, v_withRef_2308_);
lean_closure_set(v___f_2309_, 2, v_toBind_2306_);
lean_closure_set(v___f_2309_, 3, v_getRef_2307_);
v___x_2310_ = lean_apply_4(v_toBind_2306_, lean_box(0), lean_box(0), v_getRef_2307_, v___f_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_00_u03b1_2314_, lean_object* v_x_2315_){
_start:
{
lean_object* v_toBind_2316_; lean_object* v_getRef_2317_; lean_object* v_withRef_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v_toBind_2316_ = lean_ctor_get(v_inst_2312_, 1);
lean_inc_n(v_toBind_2316_, 2);
lean_dec_ref(v_inst_2312_);
v_getRef_2317_ = lean_ctor_get(v_inst_2313_, 0);
lean_inc_n(v_getRef_2317_, 2);
v_withRef_2318_ = lean_ctor_get(v_inst_2313_, 1);
lean_inc(v_withRef_2318_);
lean_dec_ref(v_inst_2313_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2319_, 0, v_x_2315_);
lean_closure_set(v___f_2319_, 1, v_withRef_2318_);
lean_closure_set(v___f_2319_, 2, v_toBind_2316_);
lean_closure_set(v___f_2319_, 3, v_getRef_2317_);
v___x_2320_ = lean_apply_4(v_toBind_2316_, lean_box(0), lean_box(0), v_getRef_2317_, v___f_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2330_, lean_object* v_k_2331_){
_start:
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2333_ = lean_name_eq(v_k_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
return v___x_2330_;
}
else
{
uint8_t v___x_2334_; 
v___x_2334_ = 0;
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2335_, lean_object* v_k_2336_){
_start:
{
uint8_t v___x_1783__boxed_2337_; uint8_t v_res_2338_; lean_object* v_r_2339_; 
v___x_1783__boxed_2337_ = lean_unbox(v___x_2335_);
v_res_2338_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2337_, v_k_2336_);
lean_dec(v_k_2336_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2341_, lean_object* v_p_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
if (lean_obj_tag(v_stx_2341_) == 1)
{
lean_object* v_info_2345_; lean_object* v_kind_2346_; lean_object* v_args_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_info_2345_ = lean_ctor_get(v_stx_2341_, 0);
v_kind_2346_ = lean_ctor_get(v_stx_2341_, 1);
v_args_2347_ = lean_ctor_get(v_stx_2341_, 2);
lean_inc(v_kind_2346_);
v___x_2348_ = lean_apply_1(v_p_2342_, v_kind_2346_);
v___x_2349_ = lean_unbox(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec_ref(v_a_2343_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_stx_2341_);
lean_ctor_set(v___x_2350_, 1, v_a_2344_);
return v___x_2350_;
}
else
{
lean_object* v_methods_2351_; lean_object* v_quotContext_2352_; lean_object* v_currMacroScope_2353_; lean_object* v_currRecDepth_2354_; lean_object* v_maxRecDepth_2355_; lean_object* v_ref_2356_; lean_object* v_ref_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_methods_2351_ = lean_ctor_get(v_a_2343_, 0);
lean_inc_n(v_methods_2351_, 2);
v_quotContext_2352_ = lean_ctor_get(v_a_2343_, 1);
lean_inc_n(v_quotContext_2352_, 2);
v_currMacroScope_2353_ = lean_ctor_get(v_a_2343_, 2);
lean_inc_n(v_currMacroScope_2353_, 2);
v_currRecDepth_2354_ = lean_ctor_get(v_a_2343_, 3);
lean_inc_n(v_currRecDepth_2354_, 2);
v_maxRecDepth_2355_ = lean_ctor_get(v_a_2343_, 4);
lean_inc_n(v_maxRecDepth_2355_, 2);
v_ref_2356_ = lean_ctor_get(v_a_2343_, 5);
lean_inc(v_ref_2356_);
lean_dec_ref(v_a_2343_);
v_ref_2357_ = l_Lean_replaceRef(v_stx_2341_, v_ref_2356_);
lean_dec(v_ref_2356_);
lean_inc(v_ref_2357_);
v___x_2358_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2358_, 0, v_methods_2351_);
lean_ctor_set(v___x_2358_, 1, v_quotContext_2352_);
lean_ctor_set(v___x_2358_, 2, v_currMacroScope_2353_);
lean_ctor_set(v___x_2358_, 3, v_currRecDepth_2354_);
lean_ctor_set(v___x_2358_, 4, v_maxRecDepth_2355_);
lean_ctor_set(v___x_2358_, 5, v_ref_2357_);
lean_inc_ref(v_stx_2341_);
v___x_2359_ = l_Lean_Macro_expandMacro_x3f(v_stx_2341_, v___x_2358_, v_a_2344_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
if (lean_obj_tag(v_a_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref_known(v___x_2358_, 6);
v_a_2361_ = lean_ctor_get(v___x_2359_, 1);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v___x_2359_, 0);
lean_dec(v_unused_2407_);
v___x_2363_ = v___x_2359_;
v_isShared_2364_ = v_isSharedCheck_2406_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2359_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2406_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_nat_dec_eq(v_currRecDepth_2354_, v_maxRecDepth_2355_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2397_; 
lean_inc_ref(v_args_2347_);
lean_inc(v_kind_2346_);
lean_inc(v_info_2345_);
lean_del_object(v___x_2363_);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_stx_2341_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2398_ = lean_ctor_get(v_stx_2341_, 2);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_stx_2341_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_stx_2341_, 0);
lean_dec(v_unused_2400_);
v___x_2367_ = v_stx_2341_;
v_isShared_2368_ = v_isSharedCheck_2397_;
goto v_resetjp_2366_;
}
else
{
lean_dec(v_stx_2341_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2397_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; size_t v_sz_2372_; size_t v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_currRecDepth_2354_, v___x_2369_);
lean_dec(v_currRecDepth_2354_);
v___x_2371_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2371_, 0, v_methods_2351_);
lean_ctor_set(v___x_2371_, 1, v_quotContext_2352_);
lean_ctor_set(v___x_2371_, 2, v_currMacroScope_2353_);
lean_ctor_set(v___x_2371_, 3, v___x_2370_);
lean_ctor_set(v___x_2371_, 4, v_maxRecDepth_2355_);
lean_ctor_set(v___x_2371_, 5, v_ref_2357_);
v_sz_2372_ = lean_array_size(v_args_2347_);
v___x_2373_ = ((size_t)0ULL);
v___x_2374_ = lean_unbox(v___x_2348_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2374_, v_sz_2372_, v___x_2373_, v_args_2347_, v___x_2371_, v_a_2361_);
lean_dec_ref_known(v___x_2371_, 6);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2387_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_a_2377_ = lean_ctor_get(v___x_2375_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2379_ = v___x_2375_;
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 2, v_a_2376_);
v___x_2382_ = v___x_2367_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_info_2345_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_kind_2346_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_a_2376_);
v___x_2382_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2382_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2377_);
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
lean_object* v_a_2388_; lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_del_object(v___x_2367_);
lean_dec(v_kind_2346_);
lean_dec(v_info_2345_);
v_a_2388_ = lean_ctor_get(v___x_2375_, 0);
v_a_2389_ = lean_ctor_get(v___x_2375_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2375_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_inc(v_a_2388_);
lean_dec(v___x_2375_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2388_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_dec(v_ref_2357_);
lean_dec(v_maxRecDepth_2355_);
lean_dec(v_currRecDepth_2354_);
lean_dec(v_currMacroScope_2353_);
lean_dec(v_quotContext_2352_);
lean_dec(v_methods_2351_);
v___x_2401_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_stx_2341_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2402_);
v___x_2404_ = v___x_2363_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_a_2361_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v_val_2409_; lean_object* v___f_2410_; 
lean_dec(v_ref_2357_);
lean_dec(v_maxRecDepth_2355_);
lean_dec(v_currRecDepth_2354_);
lean_dec(v_currMacroScope_2353_);
lean_dec(v_quotContext_2352_);
lean_dec(v_methods_2351_);
lean_dec_ref_known(v_stx_2341_, 3);
v_a_2408_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2359_, 2);
v_val_2409_ = lean_ctor_get(v_a_2360_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v_a_2360_, 1);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2410_, 0, v___x_2348_);
v_stx_2341_ = v_val_2409_;
v_p_2342_ = v___f_2410_;
v_a_2343_ = v___x_2358_;
v_a_2344_ = v_a_2408_;
goto _start;
}
}
else
{
lean_object* v_a_2412_; lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref_known(v___x_2358_, 6);
lean_dec(v_ref_2357_);
lean_dec(v_maxRecDepth_2355_);
lean_dec(v_currRecDepth_2354_);
lean_dec(v_currMacroScope_2353_);
lean_dec(v_quotContext_2352_);
lean_dec(v_methods_2351_);
lean_dec_ref_known(v_stx_2341_, 3);
v_a_2412_ = lean_ctor_get(v___x_2359_, 0);
v_a_2413_ = lean_ctor_get(v___x_2359_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2359_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_inc(v_a_2412_);
lean_dec(v___x_2359_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2412_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
lean_object* v___x_2421_; 
lean_dec_ref(v_a_2343_);
lean_dec_ref(v_p_2342_);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_stx_2341_);
lean_ctor_set(v___x_2421_, 1, v_a_2344_);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2422_, size_t v_sz_2423_, size_t v_i_2424_, lean_object* v_bs_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_usize_dec_lt(v_i_2424_, v_sz_2423_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_bs_2425_);
lean_ctor_set(v___x_2429_, 1, v___y_2427_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v_v_2432_; lean_object* v___x_2433_; 
v___x_2430_ = lean_box(v___x_2422_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2431_, 0, v___x_2430_);
v_v_2432_ = lean_array_uget_borrowed(v_bs_2425_, v_i_2424_);
lean_inc_ref(v___y_2426_);
lean_inc(v_v_2432_);
v___x_2433_ = l_Lean_expandMacros(v_v_2432_, v___f_2431_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v_a_2435_; lean_object* v___x_2436_; lean_object* v_bs_x27_2437_; size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
v_a_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2433_, 2);
v___x_2436_ = lean_unsigned_to_nat(0u);
v_bs_x27_2437_ = lean_array_uset(v_bs_2425_, v_i_2424_, v___x_2436_);
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_add(v_i_2424_, v___x_2438_);
v___x_2440_ = lean_array_uset(v_bs_x27_2437_, v_i_2424_, v_a_2434_);
v_i_2424_ = v___x_2439_;
v_bs_2425_ = v___x_2440_;
v___y_2427_ = v_a_2435_;
goto _start;
}
else
{
lean_object* v_a_2442_; lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_bs_2425_);
v_a_2442_ = lean_ctor_get(v___x_2433_, 0);
v_a_2443_ = lean_ctor_get(v___x_2433_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2433_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_inc(v_a_2442_);
lean_dec(v___x_2433_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2442_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2451_, lean_object* v_sz_2452_, lean_object* v_i_2453_, lean_object* v_bs_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v___x_1802__boxed_2457_; size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v___x_1802__boxed_2457_ = lean_unbox(v___x_2451_);
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2452_);
lean_dec(v_sz_2452_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1802__boxed_2457_, v_sz_boxed_2458_, v_i_boxed_2459_, v_bs_2454_, v___y_2455_, v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2461_, lean_object* v_val_2462_, uint8_t v_canonical_2463_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2464_ = l_Lean_SourceInfo_fromRef(v_src_2461_, v_canonical_2463_);
v___x_2465_ = 1;
lean_inc(v_val_2462_);
v___x_2466_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2462_, v___x_2465_);
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = lean_string_utf8_byte_size(v___x_2466_);
v___x_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2467_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2464_);
lean_ctor_set(v___x_2471_, 1, v___x_2469_);
lean_ctor_set(v___x_2471_, 2, v_val_2462_);
lean_ctor_set(v___x_2471_, 3, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2472_, lean_object* v_val_2473_, lean_object* v_canonical_2474_){
_start:
{
uint8_t v_canonical_boxed_2475_; lean_object* v_res_2476_; 
v_canonical_boxed_2475_ = lean_unbox(v_canonical_2474_);
v_res_2476_ = l_Lean_mkIdentFrom(v_src_2472_, v_val_2473_, v_canonical_boxed_2475_);
lean_dec(v_src_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2477_, uint8_t v_canonical_2478_, lean_object* v_toPure_2479_, lean_object* v_____do__lift_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = l_Lean_mkIdentFrom(v_____do__lift_2480_, v_val_2477_, v_canonical_2478_);
v___x_2482_ = lean_apply_2(v_toPure_2479_, lean_box(0), v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2483_, lean_object* v_canonical_2484_, lean_object* v_toPure_2485_, lean_object* v_____do__lift_2486_){
_start:
{
uint8_t v_canonical_boxed_2487_; lean_object* v_res_2488_; 
v_canonical_boxed_2487_ = lean_unbox(v_canonical_2484_);
v_res_2488_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2483_, v_canonical_boxed_2487_, v_toPure_2485_, v_____do__lift_2486_);
lean_dec(v_____do__lift_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_val_2491_, uint8_t v_canonical_2492_){
_start:
{
lean_object* v_toApplicative_2493_; lean_object* v_toBind_2494_; lean_object* v_getRef_2495_; lean_object* v_toPure_2496_; lean_object* v___x_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; 
v_toApplicative_2493_ = lean_ctor_get(v_inst_2489_, 0);
lean_inc_ref(v_toApplicative_2493_);
v_toBind_2494_ = lean_ctor_get(v_inst_2489_, 1);
lean_inc(v_toBind_2494_);
lean_dec_ref(v_inst_2489_);
v_getRef_2495_ = lean_ctor_get(v_inst_2490_, 0);
lean_inc(v_getRef_2495_);
lean_dec_ref(v_inst_2490_);
v_toPure_2496_ = lean_ctor_get(v_toApplicative_2493_, 1);
lean_inc(v_toPure_2496_);
lean_dec_ref(v_toApplicative_2493_);
v___x_2497_ = lean_box(v_canonical_2492_);
v___f_2498_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2498_, 0, v_val_2491_);
lean_closure_set(v___f_2498_, 1, v___x_2497_);
lean_closure_set(v___f_2498_, 2, v_toPure_2496_);
v___x_2499_ = lean_apply_4(v_toBind_2494_, lean_box(0), lean_box(0), v_getRef_2495_, v___f_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_val_2502_, lean_object* v_canonical_2503_){
_start:
{
uint8_t v_canonical_boxed_2504_; lean_object* v_res_2505_; 
v_canonical_boxed_2504_ = lean_unbox(v_canonical_2503_);
v_res_2505_ = l_Lean_mkIdentFromRef___redArg(v_inst_2500_, v_inst_2501_, v_val_2502_, v_canonical_boxed_2504_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_val_2509_, uint8_t v_canonical_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_mkIdentFromRef___redArg(v_inst_2507_, v_inst_2508_, v_val_2509_, v_canonical_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_val_2515_, lean_object* v_canonical_2516_){
_start:
{
uint8_t v_canonical_boxed_2517_; lean_object* v_res_2518_; 
v_canonical_boxed_2517_ = lean_unbox(v_canonical_2516_);
v_res_2518_ = l_Lean_mkIdentFromRef(v_m_2512_, v_inst_2513_, v_inst_2514_, v_val_2515_, v_canonical_boxed_2517_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2522_, lean_object* v_c_2523_, uint8_t v_canonical_2524_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v_id_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2525_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2526_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2523_);
v_id_2527_ = l_Lean_addMacroScope(v___x_2525_, v_c_2523_, v___x_2526_);
v___x_2528_ = l_Lean_SourceInfo_fromRef(v_src_2522_, v_canonical_2524_);
v___x_2529_ = 1;
lean_inc(v_id_2527_);
v___x_2530_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2527_, v___x_2529_);
v___x_2531_ = lean_string_utf8_byte_size(v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2526_);
lean_ctor_set(v___x_2532_, 2, v___x_2531_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2534_, 0, v_c_2523_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v___x_2533_);
v___x_2536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2528_);
lean_ctor_set(v___x_2536_, 1, v___x_2532_);
lean_ctor_set(v___x_2536_, 2, v_id_2527_);
lean_ctor_set(v___x_2536_, 3, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2537_, lean_object* v_c_2538_, lean_object* v_canonical_2539_){
_start:
{
uint8_t v_canonical_boxed_2540_; lean_object* v_res_2541_; 
v_canonical_boxed_2540_ = lean_unbox(v_canonical_2539_);
v_res_2541_ = l_Lean_mkCIdentFrom(v_src_2537_, v_c_2538_, v_canonical_boxed_2540_);
lean_dec(v_src_2537_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2542_, uint8_t v_canonical_2543_, lean_object* v_toPure_2544_, lean_object* v_____do__lift_2545_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = l_Lean_mkCIdentFrom(v_____do__lift_2545_, v_c_2542_, v_canonical_2543_);
v___x_2547_ = lean_apply_2(v_toPure_2544_, lean_box(0), v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2548_, lean_object* v_canonical_2549_, lean_object* v_toPure_2550_, lean_object* v_____do__lift_2551_){
_start:
{
uint8_t v_canonical_boxed_2552_; lean_object* v_res_2553_; 
v_canonical_boxed_2552_ = lean_unbox(v_canonical_2549_);
v_res_2553_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2548_, v_canonical_boxed_2552_, v_toPure_2550_, v_____do__lift_2551_);
lean_dec(v_____do__lift_2551_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_c_2556_, uint8_t v_canonical_2557_){
_start:
{
lean_object* v_toApplicative_2558_; lean_object* v_toBind_2559_; lean_object* v_getRef_2560_; lean_object* v_toPure_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; 
v_toApplicative_2558_ = lean_ctor_get(v_inst_2554_, 0);
lean_inc_ref(v_toApplicative_2558_);
v_toBind_2559_ = lean_ctor_get(v_inst_2554_, 1);
lean_inc(v_toBind_2559_);
lean_dec_ref(v_inst_2554_);
v_getRef_2560_ = lean_ctor_get(v_inst_2555_, 0);
lean_inc(v_getRef_2560_);
lean_dec_ref(v_inst_2555_);
v_toPure_2561_ = lean_ctor_get(v_toApplicative_2558_, 1);
lean_inc(v_toPure_2561_);
lean_dec_ref(v_toApplicative_2558_);
v___x_2562_ = lean_box(v_canonical_2557_);
v___f_2563_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2563_, 0, v_c_2556_);
lean_closure_set(v___f_2563_, 1, v___x_2562_);
lean_closure_set(v___f_2563_, 2, v_toPure_2561_);
v___x_2564_ = lean_apply_4(v_toBind_2559_, lean_box(0), lean_box(0), v_getRef_2560_, v___f_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_c_2567_, lean_object* v_canonical_2568_){
_start:
{
uint8_t v_canonical_boxed_2569_; lean_object* v_res_2570_; 
v_canonical_boxed_2569_ = lean_unbox(v_canonical_2568_);
v_res_2570_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2565_, v_inst_2566_, v_c_2567_, v_canonical_boxed_2569_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2571_, lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_c_2574_, uint8_t v_canonical_2575_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2572_, v_inst_2573_, v_c_2574_, v_canonical_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2577_, lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_c_2580_, lean_object* v_canonical_2581_){
_start:
{
uint8_t v_canonical_boxed_2582_; lean_object* v_res_2583_; 
v_canonical_boxed_2582_ = lean_unbox(v_canonical_2581_);
v_res_2583_ = l_Lean_mkCIdentFromRef(v_m_2577_, v_inst_2578_, v_inst_2579_, v_c_2580_, v_canonical_boxed_2582_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2584_){
_start:
{
lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_box(0);
v___x_2586_ = 0;
v___x_2587_ = l_Lean_mkCIdentFrom(v___x_2585_, v_c_2584_, v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2588_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2589_ = lean_box(2);
v___x_2590_ = 1;
lean_inc(v_val_2588_);
v___x_2591_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2588_, v___x_2590_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_string_utf8_byte_size(v___x_2591_);
v___x_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2591_);
lean_ctor_set(v___x_2594_, 1, v___x_2592_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2589_);
lean_ctor_set(v___x_2596_, 1, v___x_2594_);
lean_ctor_set(v___x_2596_, 2, v_val_2588_);
lean_ctor_set(v___x_2596_, 3, v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2602_ = lean_box(2);
v___x_2603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___x_2601_);
lean_ctor_set(v___x_2603_, 2, v_args_2600_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2604_, lean_object* v_as_2605_, size_t v_sz_2606_, size_t v_i_2607_, lean_object* v_b_2608_){
_start:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_usize_dec_lt(v_i_2607_, v_sz_2606_);
if (v___x_2609_ == 0)
{
lean_dec(v_sep_2604_);
return v_b_2608_;
}
else
{
lean_object* v_fst_2610_; lean_object* v_snd_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2631_; 
v_fst_2610_ = lean_ctor_get(v_b_2608_, 0);
v_snd_2611_ = lean_ctor_get(v_b_2608_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_b_2608_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2613_ = v_b_2608_;
v_isShared_2614_ = v_isSharedCheck_2631_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_snd_2611_);
lean_inc(v_fst_2610_);
lean_dec(v_b_2608_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2631_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v_r_2616_; lean_object* v_i_2625_; lean_object* v_a_2626_; uint8_t v___x_2627_; 
v_i_2625_ = lean_unsigned_to_nat(0u);
v_a_2626_ = lean_array_uget_borrowed(v_as_2605_, v_i_2607_);
v___x_2627_ = lean_nat_dec_lt(v_i_2625_, v_fst_2610_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_inc(v_a_2626_);
v___x_2628_ = lean_array_push(v_snd_2611_, v_a_2626_);
v_r_2616_ = v___x_2628_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_inc(v_sep_2604_);
v___x_2629_ = lean_array_push(v_snd_2611_, v_sep_2604_);
lean_inc(v_a_2626_);
v___x_2630_ = lean_array_push(v___x_2629_, v_a_2626_);
v_r_2616_ = v___x_2630_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_add(v_fst_2610_, v___x_2617_);
lean_dec(v_fst_2610_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 1, v_r_2616_);
lean_ctor_set(v___x_2613_, 0, v___x_2618_);
v___x_2620_ = v___x_2613_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_r_2616_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
size_t v___x_2621_; size_t v___x_2622_; 
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2607_, v___x_2621_);
v_i_2607_ = v___x_2622_;
v_b_2608_ = v___x_2620_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2632_, lean_object* v_as_2633_, lean_object* v_sz_2634_, lean_object* v_i_2635_, lean_object* v_b_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2634_);
lean_dec(v_sz_2634_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2632_, v_as_2633_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2636_);
lean_dec_ref(v_as_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2645_, lean_object* v_sep_2646_){
_start:
{
lean_object* v___x_2647_; size_t v_sz_2648_; size_t v___x_2649_; lean_object* v___x_2650_; lean_object* v_snd_2651_; 
v___x_2647_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2648_ = lean_array_size(v_as_2645_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2646_, v_as_2645_, v_sz_2648_, v___x_2649_, v___x_2647_);
v_snd_2651_ = lean_ctor_get(v___x_2650_, 1);
lean_inc(v_snd_2651_);
lean_dec_ref(v___x_2650_);
return v_snd_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2652_, lean_object* v_sep_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_mkSepArray(v_as_2652_, v_sep_2653_);
lean_dec_ref(v_as_2652_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2662_){
_start:
{
if (lean_obj_tag(v_arg_2662_) == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2663_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_val_2664_ = lean_ctor_get(v_arg_2662_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v_arg_2662_, 1);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_mk_empty_array_with_capacity(v___x_2665_);
v___x_2667_ = lean_array_push(v___x_2666_, v_val_2664_);
v___x_2668_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2669_ = lean_box(2);
v___x_2670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___x_2668_);
lean_ctor_set(v___x_2670_, 2, v___x_2667_);
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2677_, uint8_t v_canonical_2678_){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2679_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2680_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2681_ = l_Lean_mkAtomFrom(v_ref_2677_, v___x_2680_, v_canonical_2678_);
v___x_2682_ = lean_unsigned_to_nat(1u);
v___x_2683_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2684_ = lean_array_push(v___x_2683_, v___x_2681_);
v___x_2685_ = lean_box(2);
v___x_2686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v___x_2679_);
lean_ctor_set(v___x_2686_, 2, v___x_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2687_, lean_object* v_canonical_2688_){
_start:
{
uint8_t v_canonical_boxed_2689_; lean_object* v_res_2690_; 
v_canonical_boxed_2689_ = lean_unbox(v_canonical_2688_);
v_res_2690_ = l_Lean_mkHole(v_ref_2687_, v_canonical_boxed_2689_);
lean_dec(v_ref_2687_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2691_, lean_object* v_sep_2692_){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2693_ = l_Lean_mkSepArray(v_a_2691_, v_sep_2692_);
v___x_2694_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2695_ = lean_box(2);
v___x_2696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v___x_2694_);
lean_ctor_set(v___x_2696_, 2, v___x_2693_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2697_, lean_object* v_sep_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Syntax_mkSep(v_a_2697_, v_sep_2698_);
lean_dec_ref(v_a_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2706_, lean_object* v_elems_2707_){
_start:
{
uint8_t v___x_2708_; 
lean_inc_ref(v_sep_2706_);
v___x_2708_ = lean_string_isempty(v_sep_2706_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = l_Lean_mkAtom(v_sep_2706_);
v___x_2710_ = l_Lean_mkSepArray(v_elems_2707_, v___x_2709_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec_ref(v_sep_2706_);
v___x_2711_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2712_ = l_Lean_mkSepArray(v_elems_2707_, v___x_2711_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2713_, lean_object* v_elems_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2713_, v_elems_2714_);
lean_dec_ref(v_elems_2714_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2716_, lean_object* v_toPure_2717_, lean_object* v_sep_2718_, lean_object* v_ref_2719_){
_start:
{
lean_object* v___y_2721_; uint8_t v___x_2724_; 
lean_inc_ref(v_sep_2718_);
v___x_2724_ = lean_string_isempty(v_sep_2718_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_mkAtomFrom(v_ref_2719_, v_sep_2718_, v___x_2724_);
v___y_2721_ = v___x_2725_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2726_; 
lean_dec_ref(v_sep_2718_);
v___x_2726_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2721_ = v___x_2726_;
goto v___jp_2720_;
}
v___jp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = l_Lean_mkSepArray(v_elems_2716_, v___y_2721_);
v___x_2723_ = lean_apply_2(v_toPure_2717_, lean_box(0), v___x_2722_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2727_, lean_object* v_toPure_2728_, lean_object* v_sep_2729_, lean_object* v_ref_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2727_, v_toPure_2728_, v_sep_2729_, v_ref_2730_);
lean_dec(v_ref_2730_);
lean_dec_ref(v_elems_2727_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_sep_2734_, lean_object* v_elems_2735_){
_start:
{
lean_object* v_toApplicative_2736_; lean_object* v_toBind_2737_; lean_object* v_getRef_2738_; lean_object* v_toPure_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; 
v_toApplicative_2736_ = lean_ctor_get(v_inst_2732_, 0);
lean_inc_ref(v_toApplicative_2736_);
v_toBind_2737_ = lean_ctor_get(v_inst_2732_, 1);
lean_inc(v_toBind_2737_);
lean_dec_ref(v_inst_2732_);
v_getRef_2738_ = lean_ctor_get(v_inst_2733_, 0);
lean_inc(v_getRef_2738_);
lean_dec_ref(v_inst_2733_);
v_toPure_2739_ = lean_ctor_get(v_toApplicative_2736_, 1);
lean_inc(v_toPure_2739_);
lean_dec_ref(v_toApplicative_2736_);
v___f_2740_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2740_, 0, v_elems_2735_);
lean_closure_set(v___f_2740_, 1, v_toPure_2739_);
lean_closure_set(v___f_2740_, 2, v_sep_2734_);
v___x_2741_ = lean_apply_4(v_toBind_2737_, lean_box(0), lean_box(0), v_getRef_2738_, v___f_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_sep_2745_, lean_object* v_elems_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2743_, v_inst_2744_, v_sep_2745_, v_elems_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2748_, lean_object* v_elems_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2748_, v_elems_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2751_, lean_object* v_elems_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2751_, v_elems_2752_);
lean_dec_ref(v_elems_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2754_, lean_object* v_sep_2755_, lean_object* v_elems_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2755_, v_elems_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2758_, lean_object* v_sep_2759_, lean_object* v_elems_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2758_, v_sep_2759_, v_elems_2760_);
lean_dec_ref(v_elems_2760_);
lean_dec(v_k_2758_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2762_, lean_object* v_sep_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2764_, 0, v_k_2762_);
lean_closure_set(v___x_2764_, 1, v_sep_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = lean_array_get_size(v_x_2772_);
v___x_2774_ = lean_unsigned_to_nat(0u);
v___x_2775_ = lean_nat_dec_eq(v___x_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2776_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2777_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2778_ = lean_box(2);
v___x_2779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v___x_2777_);
lean_ctor_set(v___x_2779_, 2, v_x_2772_);
v___x_2780_ = lean_unsigned_to_nat(2u);
v___x_2781_ = lean_mk_empty_array_with_capacity(v___x_2780_);
v___x_2782_ = lean_array_push(v___x_2781_, v_fn_2771_);
v___x_2783_ = lean_array_push(v___x_2782_, v___x_2779_);
v___x_2784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2778_);
lean_ctor_set(v___x_2784_, 1, v___x_2776_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
return v___x_2784_;
}
else
{
lean_dec_ref(v_x_2772_);
return v_fn_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2785_, lean_object* v_args_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = l_Lean_mkCIdent(v_fn_2785_);
v___x_2788_ = l_Lean_Syntax_mkApp(v___x_2787_, v_args_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2789_, lean_object* v_val_2790_, lean_object* v_info_2791_){
_start:
{
lean_object* v_atom_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_atom_2792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2792_, 0, v_info_2791_);
lean_ctor_set(v_atom_2792_, 1, v_val_2790_);
v___x_2793_ = lean_unsigned_to_nat(1u);
v___x_2794_ = lean_mk_empty_array_with_capacity(v___x_2793_);
v___x_2795_ = lean_array_push(v___x_2794_, v_atom_2792_);
v___x_2796_ = lean_box(2);
v___x_2797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v_kind_2789_);
lean_ctor_set(v___x_2797_, 2, v___x_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2801_, lean_object* v_info_2802_){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2804_ = l_Char_quote(v_val_2801_);
v___x_2805_ = l_Lean_Syntax_mkLit(v___x_2803_, v___x_2804_, v_info_2802_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2806_, lean_object* v_info_2807_){
_start:
{
uint32_t v_val_boxed_2808_; lean_object* v_res_2809_; 
v_val_boxed_2808_ = lean_unbox_uint32(v_val_2806_);
lean_dec(v_val_2806_);
v_res_2809_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2808_, v_info_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2813_, lean_object* v_info_2814_){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2816_ = l_String_quote(v_val_2813_);
v___x_2817_ = l_Lean_Syntax_mkLit(v___x_2815_, v___x_2816_, v_info_2814_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2821_, lean_object* v_info_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2824_ = l_Lean_Syntax_mkLit(v___x_2823_, v_val_2821_, v_info_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2825_, lean_object* v_info_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2828_ = l_Nat_reprFast(v_val_2825_);
v___x_2829_ = l_Lean_Syntax_mkLit(v___x_2827_, v___x_2828_, v_info_2826_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2833_, lean_object* v_info_2834_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2836_ = l_Lean_Syntax_mkLit(v___x_2835_, v_val_2833_, v_info_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2840_, lean_object* v_info_2841_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2843_ = l_Lean_Syntax_mkLit(v___x_2842_, v_val_2840_, v_info_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2844_, lean_object* v_i_2845_, lean_object* v_val_2846_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_string_utf8_at_end(v_s_2844_, v_i_2845_);
if (v___x_2847_ == 0)
{
uint32_t v_c_2848_; uint32_t v___x_2849_; uint8_t v___x_2850_; 
v_c_2848_ = lean_string_utf8_get(v_s_2844_, v_i_2845_);
v___x_2849_ = 48;
v___x_2850_ = lean_uint32_dec_eq(v_c_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
uint32_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = 49;
v___x_2852_ = lean_uint32_dec_eq(v_c_2848_, v___x_2851_);
if (v___x_2852_ == 0)
{
uint32_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2853_ = 95;
v___x_2854_ = lean_uint32_dec_eq(v_c_2848_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v_val_2846_);
lean_dec(v_i_2845_);
v___x_2855_ = lean_box(0);
return v___x_2855_;
}
else
{
lean_object* v___x_2856_; 
v___x_2856_ = lean_string_utf8_next(v_s_2844_, v_i_2845_);
lean_dec(v_i_2845_);
v_i_2845_ = v___x_2856_;
goto _start;
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2858_ = lean_string_utf8_next(v_s_2844_, v_i_2845_);
lean_dec(v_i_2845_);
v___x_2859_ = lean_unsigned_to_nat(2u);
v___x_2860_ = lean_nat_mul(v___x_2859_, v_val_2846_);
lean_dec(v_val_2846_);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_add(v___x_2860_, v___x_2861_);
lean_dec(v___x_2860_);
v_i_2845_ = v___x_2858_;
v_val_2846_ = v___x_2862_;
goto _start;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_string_utf8_next(v_s_2844_, v_i_2845_);
lean_dec(v_i_2845_);
v___x_2865_ = lean_unsigned_to_nat(2u);
v___x_2866_ = lean_nat_mul(v___x_2865_, v_val_2846_);
lean_dec(v_val_2846_);
v_i_2845_ = v___x_2864_;
v_val_2846_ = v___x_2866_;
goto _start;
}
}
else
{
lean_object* v___x_2868_; 
lean_dec(v_i_2845_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_val_2846_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2869_, lean_object* v_i_2870_, lean_object* v_val_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2869_, v_i_2870_, v_val_2871_);
lean_dec_ref(v_s_2869_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2873_, lean_object* v_i_2874_, lean_object* v_val_2875_){
_start:
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_string_utf8_at_end(v_s_2873_, v_i_2874_);
if (v___x_2876_ == 0)
{
uint32_t v_c_2877_; uint8_t v___y_2879_; uint32_t v___x_2893_; uint8_t v___x_2894_; 
v_c_2877_ = lean_string_utf8_get(v_s_2873_, v_i_2874_);
v___x_2893_ = 48;
v___x_2894_ = lean_uint32_dec_le(v___x_2893_, v_c_2877_);
if (v___x_2894_ == 0)
{
v___y_2879_ = v___x_2876_;
goto v___jp_2878_;
}
else
{
uint32_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = 55;
v___x_2896_ = lean_uint32_dec_le(v_c_2877_, v___x_2895_);
v___y_2879_ = v___x_2896_;
goto v___jp_2878_;
}
v___jp_2878_:
{
if (v___y_2879_ == 0)
{
uint32_t v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = 95;
v___x_2881_ = lean_uint32_dec_eq(v_c_2877_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
lean_dec(v_val_2875_);
lean_dec(v_i_2874_);
v___x_2882_ = lean_box(0);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_string_utf8_next(v_s_2873_, v_i_2874_);
lean_dec(v_i_2874_);
v_i_2874_ = v___x_2883_;
goto _start;
}
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2885_ = lean_string_utf8_next(v_s_2873_, v_i_2874_);
lean_dec(v_i_2874_);
v___x_2886_ = lean_unsigned_to_nat(8u);
v___x_2887_ = lean_nat_mul(v___x_2886_, v_val_2875_);
lean_dec(v_val_2875_);
v___x_2888_ = lean_uint32_to_nat(v_c_2877_);
v___x_2889_ = lean_nat_add(v___x_2887_, v___x_2888_);
lean_dec(v___x_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_unsigned_to_nat(48u);
v___x_2891_ = lean_nat_sub(v___x_2889_, v___x_2890_);
lean_dec(v___x_2889_);
v_i_2874_ = v___x_2885_;
v_val_2875_ = v___x_2891_;
goto _start;
}
}
}
else
{
lean_object* v___x_2897_; 
lean_dec(v_i_2874_);
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_val_2875_);
return v___x_2897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2898_, lean_object* v_i_2899_, lean_object* v_val_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2898_, v_i_2899_, v_val_2900_);
lean_dec_ref(v_s_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2902_, lean_object* v_i_2903_){
_start:
{
uint32_t v_c_2904_; lean_object* v_i_2905_; uint32_t v___x_2932_; uint8_t v___x_2933_; 
v_c_2904_ = lean_string_utf8_get(v_s_2902_, v_i_2903_);
v_i_2905_ = lean_string_utf8_next(v_s_2902_, v_i_2903_);
v___x_2932_ = 48;
v___x_2933_ = lean_uint32_dec_le(v___x_2932_, v_c_2904_);
if (v___x_2933_ == 0)
{
goto v___jp_2920_;
}
else
{
uint32_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = 57;
v___x_2935_ = lean_uint32_dec_le(v_c_2904_, v___x_2934_);
if (v___x_2935_ == 0)
{
goto v___jp_2920_;
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2936_ = lean_uint32_to_nat(v_c_2904_);
v___x_2937_ = lean_unsigned_to_nat(48u);
v___x_2938_ = lean_nat_sub(v___x_2936_, v___x_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v_i_2905_);
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
v___jp_2906_:
{
uint32_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = 65;
v___x_2908_ = lean_uint32_dec_le(v___x_2907_, v_c_2904_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
lean_dec(v_i_2905_);
v___x_2909_ = lean_box(0);
return v___x_2909_;
}
else
{
uint32_t v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = 70;
v___x_2911_ = lean_uint32_dec_le(v_c_2904_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; 
lean_dec(v_i_2905_);
v___x_2912_ = lean_box(0);
return v___x_2912_;
}
else
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2913_ = lean_unsigned_to_nat(10u);
v___x_2914_ = lean_uint32_to_nat(v_c_2904_);
v___x_2915_ = lean_nat_add(v___x_2913_, v___x_2914_);
lean_dec(v___x_2914_);
v___x_2916_ = lean_unsigned_to_nat(65u);
v___x_2917_ = lean_nat_sub(v___x_2915_, v___x_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_i_2905_);
v___x_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
v___jp_2920_:
{
uint32_t v___x_2921_; uint8_t v___x_2922_; 
v___x_2921_ = 97;
v___x_2922_ = lean_uint32_dec_le(v___x_2921_, v_c_2904_);
if (v___x_2922_ == 0)
{
goto v___jp_2906_;
}
else
{
uint32_t v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = 102;
v___x_2924_ = lean_uint32_dec_le(v_c_2904_, v___x_2923_);
if (v___x_2924_ == 0)
{
goto v___jp_2906_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2925_ = lean_unsigned_to_nat(10u);
v___x_2926_ = lean_uint32_to_nat(v_c_2904_);
v___x_2927_ = lean_nat_add(v___x_2925_, v___x_2926_);
lean_dec(v___x_2926_);
v___x_2928_ = lean_unsigned_to_nat(97u);
v___x_2929_ = lean_nat_sub(v___x_2927_, v___x_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_i_2905_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2941_, lean_object* v_i_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2941_, v_i_2942_);
lean_dec(v_i_2942_);
lean_dec_ref(v_s_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2944_, lean_object* v_i_2945_, lean_object* v_val_2946_){
_start:
{
uint8_t v___x_2947_; 
v___x_2947_ = lean_string_utf8_at_end(v_s_2944_, v_i_2945_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2944_, v_i_2945_);
if (lean_obj_tag(v___x_2948_) == 0)
{
uint32_t v___x_2949_; uint32_t v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = lean_string_utf8_get(v_s_2944_, v_i_2945_);
v___x_2950_ = 95;
v___x_2951_ = lean_uint32_dec_eq(v___x_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v_val_2946_);
lean_dec(v_i_2945_);
v___x_2952_ = lean_box(0);
return v___x_2952_;
}
else
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_string_utf8_next(v_s_2944_, v_i_2945_);
lean_dec(v_i_2945_);
v_i_2945_ = v___x_2953_;
goto _start;
}
}
else
{
lean_object* v_val_2955_; lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v_i_2945_);
v_val_2955_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_val_2955_);
lean_dec_ref_known(v___x_2948_, 1);
v_fst_2956_ = lean_ctor_get(v_val_2955_, 0);
lean_inc(v_fst_2956_);
v_snd_2957_ = lean_ctor_get(v_val_2955_, 1);
lean_inc(v_snd_2957_);
lean_dec(v_val_2955_);
v___x_2958_ = lean_unsigned_to_nat(16u);
v___x_2959_ = lean_nat_mul(v___x_2958_, v_val_2946_);
lean_dec(v_val_2946_);
v___x_2960_ = lean_nat_add(v___x_2959_, v_fst_2956_);
lean_dec(v_fst_2956_);
lean_dec(v___x_2959_);
v_i_2945_ = v_snd_2957_;
v_val_2946_ = v___x_2960_;
goto _start;
}
}
else
{
lean_object* v___x_2962_; 
lean_dec(v_i_2945_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_val_2946_);
return v___x_2962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_2963_, lean_object* v_i_2964_, lean_object* v_val_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2963_, v_i_2964_, v_val_2965_);
lean_dec_ref(v_s_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_2967_, lean_object* v_i_2968_, lean_object* v_val_2969_){
_start:
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_string_utf8_at_end(v_s_2967_, v_i_2968_);
if (v___x_2970_ == 0)
{
uint32_t v_c_2971_; uint8_t v___y_2973_; uint32_t v___x_2987_; uint8_t v___x_2988_; 
v_c_2971_ = lean_string_utf8_get(v_s_2967_, v_i_2968_);
v___x_2987_ = 48;
v___x_2988_ = lean_uint32_dec_le(v___x_2987_, v_c_2971_);
if (v___x_2988_ == 0)
{
v___y_2973_ = v___x_2970_;
goto v___jp_2972_;
}
else
{
uint32_t v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = 57;
v___x_2990_ = lean_uint32_dec_le(v_c_2971_, v___x_2989_);
v___y_2973_ = v___x_2990_;
goto v___jp_2972_;
}
v___jp_2972_:
{
if (v___y_2973_ == 0)
{
uint32_t v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = 95;
v___x_2975_ = lean_uint32_dec_eq(v_c_2971_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v_val_2969_);
lean_dec(v_i_2968_);
v___x_2976_ = lean_box(0);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_string_utf8_next(v_s_2967_, v_i_2968_);
lean_dec(v_i_2968_);
v_i_2968_ = v___x_2977_;
goto _start;
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2979_ = lean_string_utf8_next(v_s_2967_, v_i_2968_);
lean_dec(v_i_2968_);
v___x_2980_ = lean_unsigned_to_nat(10u);
v___x_2981_ = lean_nat_mul(v___x_2980_, v_val_2969_);
lean_dec(v_val_2969_);
v___x_2982_ = lean_uint32_to_nat(v_c_2971_);
v___x_2983_ = lean_nat_add(v___x_2981_, v___x_2982_);
lean_dec(v___x_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_unsigned_to_nat(48u);
v___x_2985_ = lean_nat_sub(v___x_2983_, v___x_2984_);
lean_dec(v___x_2983_);
v_i_2968_ = v___x_2979_;
v_val_2969_ = v___x_2985_;
goto _start;
}
}
}
else
{
lean_object* v___x_2991_; 
lean_dec(v_i_2968_);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_val_2969_);
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_2992_, lean_object* v_i_2993_, lean_object* v_val_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2992_, v_i_2993_, v_val_2994_);
lean_dec_ref(v_s_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_2998_){
_start:
{
lean_object* v_len_2999_; lean_object* v___x_3000_; uint8_t v___x_3010_; 
v_len_2999_ = lean_string_length(v_s_2998_);
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_nat_dec_eq(v_len_2999_, v___x_3000_);
if (v___x_3010_ == 0)
{
uint32_t v_c_3011_; uint32_t v___x_3012_; uint8_t v___x_3013_; 
v_c_3011_ = lean_string_utf8_get(v_s_2998_, v___x_3000_);
v___x_3012_ = 48;
v___x_3013_ = lean_uint32_dec_eq(v_c_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
uint8_t v___x_3014_; 
lean_dec(v_len_2999_);
v___x_3014_ = lean_uint32_dec_le(v___x_3012_, v_c_3011_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_box(0);
return v___x_3015_;
}
else
{
uint32_t v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = 57;
v___x_3017_ = lean_uint32_dec_le(v_c_3011_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_box(0);
return v___x_3018_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2998_, v___x_3000_, v___x_3000_);
return v___x_3019_;
}
}
}
else
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = lean_unsigned_to_nat(1u);
v___x_3021_ = lean_nat_dec_eq(v_len_2999_, v___x_3020_);
lean_dec(v_len_2999_);
if (v___x_3021_ == 0)
{
uint32_t v_c_3022_; uint32_t v___x_3023_; uint8_t v___x_3024_; 
v_c_3022_ = lean_string_utf8_get(v_s_2998_, v___x_3020_);
v___x_3023_ = 120;
v___x_3024_ = lean_uint32_dec_eq(v_c_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
uint32_t v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = 88;
v___x_3026_ = lean_uint32_dec_eq(v_c_3022_, v___x_3025_);
if (v___x_3026_ == 0)
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 98;
v___x_3028_ = lean_uint32_dec_eq(v_c_3022_, v___x_3027_);
if (v___x_3028_ == 0)
{
uint32_t v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = 66;
v___x_3030_ = lean_uint32_dec_eq(v_c_3022_, v___x_3029_);
if (v___x_3030_ == 0)
{
uint32_t v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = 111;
v___x_3032_ = lean_uint32_dec_eq(v_c_3022_, v___x_3031_);
if (v___x_3032_ == 0)
{
uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = 79;
v___x_3034_ = lean_uint32_dec_eq(v_c_3022_, v___x_3033_);
if (v___x_3034_ == 0)
{
uint8_t v___x_3035_; 
v___x_3035_ = lean_uint32_dec_le(v___x_3012_, v_c_3022_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_box(0);
return v___x_3036_;
}
else
{
uint32_t v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = 57;
v___x_3038_ = lean_uint32_dec_le(v_c_3022_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_box(0);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2998_, v___x_3000_, v___x_3000_);
return v___x_3040_;
}
}
}
else
{
goto v___jp_3001_;
}
}
else
{
goto v___jp_3001_;
}
}
else
{
goto v___jp_3004_;
}
}
else
{
goto v___jp_3004_;
}
}
else
{
goto v___jp_3007_;
}
}
else
{
goto v___jp_3007_;
}
}
else
{
lean_object* v___x_3041_; 
v___x_3041_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3041_;
}
}
}
else
{
lean_object* v___x_3042_; 
lean_dec(v_len_2999_);
v___x_3042_ = lean_box(0);
return v___x_3042_;
}
v___jp_3001_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_unsigned_to_nat(2u);
v___x_3003_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2998_, v___x_3002_, v___x_3000_);
return v___x_3003_;
}
v___jp_3004_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_unsigned_to_nat(2u);
v___x_3006_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2998_, v___x_3005_, v___x_3000_);
return v___x_3006_;
}
v___jp_3007_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_unsigned_to_nat(2u);
v___x_3009_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2998_, v___x_3008_, v___x_3000_);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3043_);
lean_dec_ref(v_s_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3045_, lean_object* v_stx_3046_){
_start:
{
if (lean_obj_tag(v_stx_3046_) == 1)
{
lean_object* v_kind_3047_; lean_object* v_args_3048_; uint8_t v___y_3050_; uint8_t v___x_3057_; 
v_kind_3047_ = lean_ctor_get(v_stx_3046_, 1);
v_args_3048_ = lean_ctor_get(v_stx_3046_, 2);
v___x_3057_ = lean_name_eq(v_kind_3047_, v_litKind_3045_);
if (v___x_3057_ == 0)
{
v___y_3050_ = v___x_3057_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3058_ = lean_array_get_size(v_args_3048_);
v___x_3059_ = lean_unsigned_to_nat(1u);
v___x_3060_ = lean_nat_dec_eq(v___x_3058_, v___x_3059_);
v___y_3050_ = v___x_3060_;
goto v___jp_3049_;
}
v___jp_3049_:
{
if (v___y_3050_ == 0)
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_box(0);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(0u);
v___x_3053_ = lean_array_fget_borrowed(v_args_3048_, v___x_3052_);
if (lean_obj_tag(v___x_3053_) == 2)
{
lean_object* v_val_3054_; lean_object* v___x_3055_; 
v_val_3054_ = lean_ctor_get(v___x_3053_, 1);
lean_inc_ref(v_val_3054_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_val_3054_);
return v___x_3055_;
}
else
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_box(0);
return v___x_3056_;
}
}
}
}
else
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_box(0);
return v___x_3061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3062_, lean_object* v_stx_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Syntax_isLit_x3f(v_litKind_3062_, v_stx_3063_);
lean_dec(v_stx_3063_);
lean_dec(v_litKind_3062_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3065_, lean_object* v_stx_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_Syntax_isLit_x3f(v_litKind_3065_, v_stx_3066_);
if (lean_obj_tag(v___x_3067_) == 1)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3068_);
lean_dec(v_val_3068_);
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; 
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
return v___x_3070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3071_, lean_object* v_stx_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3071_, v_stx_3072_);
lean_dec(v_stx_3072_);
lean_dec(v_litKind_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3074_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3076_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3075_, v_s_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Syntax_isNatLit_x3f(v_s_3077_);
lean_dec(v_s_3077_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3082_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3084_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3083_, v_s_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3085_);
lean_dec(v_s_3085_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3087_, lean_object* v_i_3088_, lean_object* v_val_3089_, lean_object* v_e_3090_, uint8_t v_sign_3091_, lean_object* v_exp_3092_){
_start:
{
uint8_t v___x_3093_; 
v___x_3093_ = lean_string_utf8_at_end(v_s_3087_, v_i_3088_);
if (v___x_3093_ == 0)
{
uint32_t v_c_3094_; uint8_t v___y_3096_; uint32_t v___x_3110_; uint8_t v___x_3111_; 
v_c_3094_ = lean_string_utf8_get(v_s_3087_, v_i_3088_);
v___x_3110_ = 48;
v___x_3111_ = lean_uint32_dec_le(v___x_3110_, v_c_3094_);
if (v___x_3111_ == 0)
{
v___y_3096_ = v___x_3093_;
goto v___jp_3095_;
}
else
{
uint32_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = 57;
v___x_3113_ = lean_uint32_dec_le(v_c_3094_, v___x_3112_);
v___y_3096_ = v___x_3113_;
goto v___jp_3095_;
}
v___jp_3095_:
{
if (v___y_3096_ == 0)
{
uint32_t v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = 95;
v___x_3098_ = lean_uint32_dec_eq(v_c_3094_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; 
lean_dec(v_exp_3092_);
lean_dec(v_val_3089_);
lean_dec(v_i_3088_);
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_string_utf8_next(v_s_3087_, v_i_3088_);
lean_dec(v_i_3088_);
v_i_3088_ = v___x_3100_;
goto _start;
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3102_ = lean_string_utf8_next(v_s_3087_, v_i_3088_);
lean_dec(v_i_3088_);
v___x_3103_ = lean_unsigned_to_nat(10u);
v___x_3104_ = lean_nat_mul(v___x_3103_, v_exp_3092_);
lean_dec(v_exp_3092_);
v___x_3105_ = lean_uint32_to_nat(v_c_3094_);
v___x_3106_ = lean_nat_add(v___x_3104_, v___x_3105_);
lean_dec(v___x_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_unsigned_to_nat(48u);
v___x_3108_ = lean_nat_sub(v___x_3106_, v___x_3107_);
lean_dec(v___x_3106_);
v_i_3088_ = v___x_3102_;
v_exp_3092_ = v___x_3108_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3088_);
if (v_sign_3091_ == 0)
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_nat_dec_le(v_e_3090_, v_exp_3092_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3115_ = lean_nat_sub(v_e_3090_, v_exp_3092_);
lean_dec(v_exp_3092_);
v___x_3116_ = lean_box(v___x_3093_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3115_);
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v_val_3089_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3120_ = lean_nat_sub(v_exp_3092_, v_e_3090_);
lean_dec(v_exp_3092_);
v___x_3121_ = lean_box(v_sign_3091_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3120_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_val_3089_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3125_ = lean_nat_add(v_exp_3092_, v_e_3090_);
lean_dec(v_exp_3092_);
v___x_3126_ = lean_box(v_sign_3091_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3125_);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v_val_3089_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
return v___x_3129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3130_, lean_object* v_i_3131_, lean_object* v_val_3132_, lean_object* v_e_3133_, lean_object* v_sign_3134_, lean_object* v_exp_3135_){
_start:
{
uint8_t v_sign_boxed_3136_; lean_object* v_res_3137_; 
v_sign_boxed_3136_ = lean_unbox(v_sign_3134_);
v_res_3137_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3130_, v_i_3131_, v_val_3132_, v_e_3133_, v_sign_boxed_3136_, v_exp_3135_);
lean_dec(v_e_3133_);
lean_dec_ref(v_s_3130_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3138_, lean_object* v_i_3139_, lean_object* v_val_3140_, lean_object* v_e_3141_){
_start:
{
uint8_t v___x_3142_; 
v___x_3142_ = lean_string_utf8_at_end(v_s_3138_, v_i_3139_);
if (v___x_3142_ == 0)
{
uint32_t v_c_3143_; uint32_t v___x_3144_; uint8_t v___x_3145_; 
v_c_3143_ = lean_string_utf8_get(v_s_3138_, v_i_3139_);
v___x_3144_ = 45;
v___x_3145_ = lean_uint32_dec_eq(v_c_3143_, v___x_3144_);
if (v___x_3145_ == 0)
{
uint32_t v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = 43;
v___x_3147_ = lean_uint32_dec_eq(v_c_3143_, v___x_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3138_, v_i_3139_, v_val_3140_, v_e_3141_, v___x_3147_, v___x_3148_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = lean_string_utf8_next(v_s_3138_, v_i_3139_);
lean_dec(v_i_3139_);
v___x_3151_ = lean_unsigned_to_nat(0u);
v___x_3152_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3138_, v___x_3150_, v_val_3140_, v_e_3141_, v___x_3145_, v___x_3151_);
return v___x_3152_;
}
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = lean_string_utf8_next(v_s_3138_, v_i_3139_);
lean_dec(v_i_3139_);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3138_, v___x_3153_, v_val_3140_, v_e_3141_, v___x_3145_, v___x_3154_);
return v___x_3155_;
}
}
else
{
lean_object* v___x_3156_; 
lean_dec(v_val_3140_);
lean_dec(v_i_3139_);
v___x_3156_ = lean_box(0);
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3157_, lean_object* v_i_3158_, lean_object* v_val_3159_, lean_object* v_e_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3157_, v_i_3158_, v_val_3159_, v_e_3160_);
lean_dec(v_e_3160_);
lean_dec_ref(v_s_3157_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3162_, lean_object* v_i_3163_, lean_object* v_val_3164_, lean_object* v_e_3165_){
_start:
{
uint8_t v___x_3169_; 
v___x_3169_ = lean_string_utf8_at_end(v_s_3162_, v_i_3163_);
if (v___x_3169_ == 0)
{
uint32_t v_c_3170_; uint8_t v___y_3172_; uint32_t v___x_3192_; uint8_t v___x_3193_; 
v_c_3170_ = lean_string_utf8_get(v_s_3162_, v_i_3163_);
v___x_3192_ = 48;
v___x_3193_ = lean_uint32_dec_le(v___x_3192_, v_c_3170_);
if (v___x_3193_ == 0)
{
v___y_3172_ = v___x_3169_;
goto v___jp_3171_;
}
else
{
uint32_t v___x_3194_; uint8_t v___x_3195_; 
v___x_3194_ = 57;
v___x_3195_ = lean_uint32_dec_le(v_c_3170_, v___x_3194_);
v___y_3172_ = v___x_3195_;
goto v___jp_3171_;
}
v___jp_3171_:
{
if (v___y_3172_ == 0)
{
uint32_t v___x_3173_; uint8_t v___x_3174_; 
v___x_3173_ = 95;
v___x_3174_ = lean_uint32_dec_eq(v_c_3170_, v___x_3173_);
if (v___x_3174_ == 0)
{
uint32_t v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = 101;
v___x_3176_ = lean_uint32_dec_eq(v_c_3170_, v___x_3175_);
if (v___x_3176_ == 0)
{
uint32_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = 69;
v___x_3178_ = lean_uint32_dec_eq(v_c_3170_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_dec(v_e_3165_);
lean_dec(v_val_3164_);
lean_dec(v_i_3163_);
v___x_3179_ = lean_box(0);
return v___x_3179_;
}
else
{
goto v___jp_3166_;
}
}
else
{
goto v___jp_3166_;
}
}
else
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_string_utf8_next(v_s_3162_, v_i_3163_);
lean_dec(v_i_3163_);
v_i_3163_ = v___x_3180_;
goto _start;
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3182_ = lean_string_utf8_next(v_s_3162_, v_i_3163_);
lean_dec(v_i_3163_);
v___x_3183_ = lean_unsigned_to_nat(10u);
v___x_3184_ = lean_nat_mul(v___x_3183_, v_val_3164_);
lean_dec(v_val_3164_);
v___x_3185_ = lean_uint32_to_nat(v_c_3170_);
v___x_3186_ = lean_nat_add(v___x_3184_, v___x_3185_);
lean_dec(v___x_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_unsigned_to_nat(48u);
v___x_3188_ = lean_nat_sub(v___x_3186_, v___x_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_unsigned_to_nat(1u);
v___x_3190_ = lean_nat_add(v_e_3165_, v___x_3189_);
lean_dec(v_e_3165_);
v_i_3163_ = v___x_3182_;
v_val_3164_ = v___x_3188_;
v_e_3165_ = v___x_3190_;
goto _start;
}
}
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_dec(v_i_3163_);
v___x_3196_ = lean_box(v___x_3169_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v_e_3165_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_val_3164_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
v___jp_3166_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_string_utf8_next(v_s_3162_, v_i_3163_);
lean_dec(v_i_3163_);
v___x_3168_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3162_, v___x_3167_, v_val_3164_, v_e_3165_);
lean_dec(v_e_3165_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3200_, lean_object* v_i_3201_, lean_object* v_val_3202_, lean_object* v_e_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3200_, v_i_3201_, v_val_3202_, v_e_3203_);
lean_dec_ref(v_s_3200_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3205_, lean_object* v_i_3206_, lean_object* v_val_3207_){
_start:
{
uint8_t v___x_3212_; 
v___x_3212_ = lean_string_utf8_at_end(v_s_3205_, v_i_3206_);
if (v___x_3212_ == 0)
{
uint32_t v_c_3213_; uint8_t v___y_3215_; uint32_t v___x_3238_; uint8_t v___x_3239_; 
v_c_3213_ = lean_string_utf8_get(v_s_3205_, v_i_3206_);
v___x_3238_ = 48;
v___x_3239_ = lean_uint32_dec_le(v___x_3238_, v_c_3213_);
if (v___x_3239_ == 0)
{
v___y_3215_ = v___x_3212_;
goto v___jp_3214_;
}
else
{
uint32_t v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = 57;
v___x_3241_ = lean_uint32_dec_le(v_c_3213_, v___x_3240_);
v___y_3215_ = v___x_3241_;
goto v___jp_3214_;
}
v___jp_3214_:
{
if (v___y_3215_ == 0)
{
uint32_t v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = 95;
v___x_3217_ = lean_uint32_dec_eq(v_c_3213_, v___x_3216_);
if (v___x_3217_ == 0)
{
uint32_t v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = 46;
v___x_3219_ = lean_uint32_dec_eq(v_c_3213_, v___x_3218_);
if (v___x_3219_ == 0)
{
uint32_t v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = 101;
v___x_3221_ = lean_uint32_dec_eq(v_c_3213_, v___x_3220_);
if (v___x_3221_ == 0)
{
uint32_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3222_ = 69;
v___x_3223_ = lean_uint32_dec_eq(v_c_3213_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec(v_val_3207_);
lean_dec(v_i_3206_);
v___x_3224_ = lean_box(0);
return v___x_3224_;
}
else
{
goto v___jp_3208_;
}
}
else
{
goto v___jp_3208_;
}
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3225_ = lean_string_utf8_next(v_s_3205_, v_i_3206_);
lean_dec(v_i_3206_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3205_, v___x_3225_, v_val_3207_, v___x_3226_);
return v___x_3227_;
}
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_string_utf8_next(v_s_3205_, v_i_3206_);
lean_dec(v_i_3206_);
v_i_3206_ = v___x_3228_;
goto _start;
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3230_ = lean_string_utf8_next(v_s_3205_, v_i_3206_);
lean_dec(v_i_3206_);
v___x_3231_ = lean_unsigned_to_nat(10u);
v___x_3232_ = lean_nat_mul(v___x_3231_, v_val_3207_);
lean_dec(v_val_3207_);
v___x_3233_ = lean_uint32_to_nat(v_c_3213_);
v___x_3234_ = lean_nat_add(v___x_3232_, v___x_3233_);
lean_dec(v___x_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_unsigned_to_nat(48u);
v___x_3236_ = lean_nat_sub(v___x_3234_, v___x_3235_);
lean_dec(v___x_3234_);
v_i_3206_ = v___x_3230_;
v_val_3207_ = v___x_3236_;
goto _start;
}
}
}
else
{
lean_object* v___x_3242_; 
lean_dec(v_val_3207_);
lean_dec(v_i_3206_);
v___x_3242_ = lean_box(0);
return v___x_3242_;
}
v___jp_3208_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = lean_string_utf8_next(v_s_3205_, v_i_3206_);
lean_dec(v_i_3206_);
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3205_, v___x_3209_, v_val_3207_, v___x_3210_);
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3243_, lean_object* v_i_3244_, lean_object* v_val_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3243_, v_i_3244_, v_val_3245_);
lean_dec_ref(v_s_3243_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3247_){
_start:
{
lean_object* v_len_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_len_3248_ = lean_string_length(v_s_3247_);
v___x_3249_ = lean_unsigned_to_nat(0u);
v___x_3250_ = lean_nat_dec_eq(v_len_3248_, v___x_3249_);
lean_dec(v_len_3248_);
if (v___x_3250_ == 0)
{
uint32_t v_c_3251_; uint32_t v___x_3252_; uint8_t v___x_3253_; 
v_c_3251_ = lean_string_utf8_get(v_s_3247_, v___x_3249_);
v___x_3252_ = 48;
v___x_3253_ = lean_uint32_dec_le(v___x_3252_, v_c_3251_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_box(0);
return v___x_3254_;
}
else
{
uint32_t v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = 57;
v___x_3256_ = lean_uint32_dec_le(v_c_3251_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_box(0);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3247_, v___x_3249_, v___x_3249_);
return v___x_3258_;
}
}
}
else
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_box(0);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3260_);
lean_dec_ref(v_s_3260_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3262_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3264_ = l_Lean_Syntax_isLit_x3f(v___x_3263_, v_stx_3262_);
if (lean_obj_tag(v___x_3264_) == 1)
{
lean_object* v_val_3265_; lean_object* v___x_3266_; 
v_val_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_val_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3265_);
lean_dec(v_val_3265_);
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; 
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3268_);
lean_dec(v_stx_3268_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3270_){
_start:
{
switch(lean_obj_tag(v_x_3270_))
{
case 2:
{
lean_object* v_val_3271_; lean_object* v___x_3272_; 
v_val_3271_ = lean_ctor_get(v_x_3270_, 1);
lean_inc_ref(v_val_3271_);
lean_dec_ref_known(v_x_3270_, 2);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_val_3271_);
return v___x_3272_;
}
case 3:
{
lean_object* v_rawVal_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_rawVal_3273_ = lean_ctor_get(v_x_3270_, 1);
lean_inc_ref(v_rawVal_3273_);
lean_dec_ref_known(v_x_3270_, 4);
v___x_3274_ = lean_substring_tostring(v_rawVal_3273_);
v___x_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
default: 
{
lean_object* v___x_3276_; 
lean_dec(v_x_3270_);
v___x_3276_ = lean_box(0);
return v___x_3276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3277_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_unsigned_to_nat(0u);
return v___x_3279_;
}
else
{
lean_object* v_val_3280_; 
v_val_3280_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_val_3280_);
lean_dec_ref_known(v___x_3278_, 1);
return v_val_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Syntax_toNat(v_stx_3281_);
lean_dec(v_stx_3281_);
return v_res_3282_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = 9;
v___x_3284_ = lean_box_uint32(v___x_3283_);
return v___x_3284_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = 10;
v___x_3286_ = lean_box_uint32(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = 13;
v___x_3288_ = lean_box_uint32(v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = 39;
v___x_3290_ = lean_box_uint32(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = 34;
v___x_3292_ = lean_box_uint32(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = 92;
v___x_3294_ = lean_box_uint32(v___x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3295_, lean_object* v_i_3296_){
_start:
{
uint32_t v_c_3297_; lean_object* v_i_3298_; uint32_t v___x_3299_; uint8_t v___x_3300_; 
v_c_3297_ = lean_string_utf8_get(v_s_3295_, v_i_3296_);
v_i_3298_ = lean_string_utf8_next(v_s_3295_, v_i_3296_);
v___x_3299_ = 92;
v___x_3300_ = lean_uint32_dec_eq(v_c_3297_, v___x_3299_);
if (v___x_3300_ == 0)
{
uint32_t v___x_3301_; uint8_t v___x_3302_; 
v___x_3301_ = 34;
v___x_3302_ = lean_uint32_dec_eq(v_c_3297_, v___x_3301_);
if (v___x_3302_ == 0)
{
uint32_t v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = 39;
v___x_3304_ = lean_uint32_dec_eq(v_c_3297_, v___x_3303_);
if (v___x_3304_ == 0)
{
uint32_t v___x_3305_; uint8_t v___x_3306_; 
v___x_3305_ = 114;
v___x_3306_ = lean_uint32_dec_eq(v_c_3297_, v___x_3305_);
if (v___x_3306_ == 0)
{
uint32_t v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = 110;
v___x_3308_ = lean_uint32_dec_eq(v_c_3297_, v___x_3307_);
if (v___x_3308_ == 0)
{
uint32_t v___x_3309_; uint8_t v___x_3310_; 
v___x_3309_ = 116;
v___x_3310_ = lean_uint32_dec_eq(v_c_3297_, v___x_3309_);
if (v___x_3310_ == 0)
{
uint32_t v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = 120;
v___x_3312_ = lean_uint32_dec_eq(v_c_3297_, v___x_3311_);
if (v___x_3312_ == 0)
{
uint32_t v___x_3313_; uint8_t v___x_3314_; 
v___x_3313_ = 117;
v___x_3314_ = lean_uint32_dec_eq(v_c_3297_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; 
lean_dec(v_i_3298_);
v___x_3315_ = lean_box(0);
return v___x_3315_;
}
else
{
lean_object* v___x_3316_; 
v___x_3316_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3295_, v_i_3298_);
lean_dec(v_i_3298_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_box(0);
return v___x_3317_;
}
else
{
lean_object* v_val_3318_; lean_object* v_fst_3319_; lean_object* v_snd_3320_; lean_object* v___x_3321_; 
v_val_3318_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3318_);
lean_dec_ref_known(v___x_3316_, 1);
v_fst_3319_ = lean_ctor_get(v_val_3318_, 0);
lean_inc(v_fst_3319_);
v_snd_3320_ = lean_ctor_get(v_val_3318_, 1);
lean_inc(v_snd_3320_);
lean_dec(v_val_3318_);
v___x_3321_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3295_, v_snd_3320_);
lean_dec(v_snd_3320_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3322_; 
lean_dec(v_fst_3319_);
v___x_3322_ = lean_box(0);
return v___x_3322_;
}
else
{
lean_object* v_val_3323_; lean_object* v_fst_3324_; lean_object* v_snd_3325_; lean_object* v___x_3326_; 
v_val_3323_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3321_, 1);
v_fst_3324_ = lean_ctor_get(v_val_3323_, 0);
lean_inc(v_fst_3324_);
v_snd_3325_ = lean_ctor_get(v_val_3323_, 1);
lean_inc(v_snd_3325_);
lean_dec(v_val_3323_);
v___x_3326_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3295_, v_snd_3325_);
lean_dec(v_snd_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3327_; 
lean_dec(v_fst_3324_);
lean_dec(v_fst_3319_);
v___x_3327_ = lean_box(0);
return v___x_3327_;
}
else
{
lean_object* v_val_3328_; lean_object* v_fst_3329_; lean_object* v_snd_3330_; lean_object* v___x_3331_; 
v_val_3328_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___x_3326_, 1);
v_fst_3329_ = lean_ctor_get(v_val_3328_, 0);
lean_inc(v_fst_3329_);
v_snd_3330_ = lean_ctor_get(v_val_3328_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_val_3328_);
v___x_3331_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3295_, v_snd_3330_);
lean_dec(v_snd_3330_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v___x_3332_; 
lean_dec(v_fst_3329_);
lean_dec(v_fst_3324_);
lean_dec(v_fst_3319_);
v___x_3332_ = lean_box(0);
return v___x_3332_;
}
else
{
lean_object* v_val_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3358_; 
v_val_3333_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3335_ = v___x_3331_;
v_isShared_3336_ = v_isSharedCheck_3358_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_val_3333_);
lean_dec(v___x_3331_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3358_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v_fst_3337_; lean_object* v_snd_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3357_; 
v_fst_3337_ = lean_ctor_get(v_val_3333_, 0);
v_snd_3338_ = lean_ctor_get(v_val_3333_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_val_3333_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3340_ = v_val_3333_;
v_isShared_3341_ = v_isSharedCheck_3357_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snd_3338_);
lean_inc(v_fst_3337_);
lean_dec(v_val_3333_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3357_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint32_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3342_ = lean_unsigned_to_nat(16u);
v___x_3343_ = lean_nat_mul(v___x_3342_, v_fst_3319_);
lean_dec(v_fst_3319_);
v___x_3344_ = lean_nat_add(v___x_3343_, v_fst_3324_);
lean_dec(v_fst_3324_);
lean_dec(v___x_3343_);
v___x_3345_ = lean_nat_mul(v___x_3342_, v___x_3344_);
lean_dec(v___x_3344_);
v___x_3346_ = lean_nat_add(v___x_3345_, v_fst_3329_);
lean_dec(v_fst_3329_);
lean_dec(v___x_3345_);
v___x_3347_ = lean_nat_mul(v___x_3342_, v___x_3346_);
lean_dec(v___x_3346_);
v___x_3348_ = lean_nat_add(v___x_3347_, v_fst_3337_);
lean_dec(v_fst_3337_);
lean_dec(v___x_3347_);
v___x_3349_ = l_Char_ofNat(v___x_3348_);
lean_dec(v___x_3348_);
v___x_3350_ = lean_box_uint32(v___x_3349_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3350_);
v___x_3352_ = v___x_3340_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_snd_3338_);
v___x_3352_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3354_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3352_);
v___x_3354_ = v___x_3335_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
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
lean_object* v___x_3359_; 
v___x_3359_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3295_, v_i_3298_);
lean_dec(v_i_3298_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_box(0);
return v___x_3360_;
}
else
{
lean_object* v_val_3361_; lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3364_; 
v_val_3361_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v___x_3359_, 1);
v_fst_3362_ = lean_ctor_get(v_val_3361_, 0);
lean_inc(v_fst_3362_);
v_snd_3363_ = lean_ctor_get(v_val_3361_, 1);
lean_inc(v_snd_3363_);
lean_dec(v_val_3361_);
v___x_3364_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3295_, v_snd_3363_);
lean_dec(v_snd_3363_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3365_; 
lean_dec(v_fst_3362_);
v___x_3365_ = lean_box(0);
return v___x_3365_;
}
else
{
lean_object* v_val_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3387_; 
v_val_3366_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3368_ = v___x_3364_;
v_isShared_3369_ = v_isSharedCheck_3387_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_val_3366_);
lean_dec(v___x_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3387_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_fst_3370_; lean_object* v_snd_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3386_; 
v_fst_3370_ = lean_ctor_get(v_val_3366_, 0);
v_snd_3371_ = lean_ctor_get(v_val_3366_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_val_3366_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3373_ = v_val_3366_;
v_isShared_3374_ = v_isSharedCheck_3386_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_snd_3371_);
lean_inc(v_fst_3370_);
lean_dec(v_val_3366_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3386_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; uint32_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3375_ = lean_unsigned_to_nat(16u);
v___x_3376_ = lean_nat_mul(v___x_3375_, v_fst_3362_);
lean_dec(v_fst_3362_);
v___x_3377_ = lean_nat_add(v___x_3376_, v_fst_3370_);
lean_dec(v_fst_3370_);
lean_dec(v___x_3376_);
v___x_3378_ = l_Char_ofNat(v___x_3377_);
lean_dec(v___x_3377_);
v___x_3379_ = lean_box_uint32(v___x_3378_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3379_);
v___x_3381_ = v___x_3373_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_snd_3371_);
v___x_3381_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v___x_3381_);
v___x_3383_ = v___x_3368_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
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
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v_i_3298_);
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v_i_3298_);
v___x_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
return v___x_3393_;
}
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v_i_3298_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v_i_3298_);
v___x_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v_i_3298_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v_i_3298_);
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3406_, lean_object* v_i_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Syntax_decodeQuotedChar(v_s_3406_, v_i_3407_);
lean_dec(v_i_3407_);
lean_dec_ref(v_s_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3409_){
_start:
{
uint32_t v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = 32;
v___x_3411_ = lean_uint32_dec_eq(v___y_3409_, v___x_3410_);
if (v___x_3411_ == 0)
{
uint32_t v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = 9;
v___x_3413_ = lean_uint32_dec_eq(v___y_3409_, v___x_3412_);
if (v___x_3413_ == 0)
{
uint32_t v___x_3414_; uint8_t v___x_3415_; 
v___x_3414_ = 13;
v___x_3415_ = lean_uint32_dec_eq(v___y_3409_, v___x_3414_);
if (v___x_3415_ == 0)
{
uint32_t v___x_3416_; uint8_t v___x_3417_; 
v___x_3416_ = 10;
v___x_3417_ = lean_uint32_dec_eq(v___y_3409_, v___x_3416_);
return v___x_3417_;
}
else
{
return v___x_3415_;
}
}
else
{
return v___x_3413_;
}
}
else
{
return v___x_3411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3418_){
_start:
{
uint32_t v___y_264__boxed_3419_; uint8_t v_res_3420_; lean_object* v_r_3421_; 
v___y_264__boxed_3419_ = lean_unbox_uint32(v___y_3418_);
lean_dec(v___y_3418_);
v_res_3420_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_264__boxed_3419_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3423_, lean_object* v_i_3424_){
_start:
{
lean_object* v___f_3425_; uint32_t v___x_3430_; uint32_t v___x_3431_; uint8_t v___x_3432_; 
v___f_3425_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3430_ = lean_string_utf8_get(v_s_3423_, v_i_3424_);
v___x_3431_ = 32;
v___x_3432_ = lean_uint32_dec_eq(v___x_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
uint32_t v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = 9;
v___x_3434_ = lean_uint32_dec_eq(v___x_3430_, v___x_3433_);
if (v___x_3434_ == 0)
{
uint32_t v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = 13;
v___x_3436_ = lean_uint32_dec_eq(v___x_3430_, v___x_3435_);
if (v___x_3436_ == 0)
{
uint32_t v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = 10;
v___x_3438_ = lean_uint32_dec_eq(v___x_3430_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_dec_ref(v_s_3423_);
v___x_3439_ = lean_box(0);
return v___x_3439_;
}
else
{
goto v___jp_3426_;
}
}
else
{
goto v___jp_3426_;
}
}
else
{
goto v___jp_3426_;
}
}
else
{
goto v___jp_3426_;
}
v___jp_3426_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = lean_string_utf8_next(v_s_3423_, v_i_3424_);
v___x_3428_ = lean_string_nextwhile(v_s_3423_, v___f_3425_, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3440_, lean_object* v_i_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Syntax_decodeStringGap(v_s_3440_, v_i_3441_);
lean_dec(v_i_3441_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3443_, lean_object* v_i_3444_, lean_object* v_acc_3445_){
_start:
{
uint32_t v_c_3446_; uint32_t v___x_3447_; uint8_t v___x_3448_; 
v_c_3446_ = lean_string_utf8_get(v_s_3443_, v_i_3444_);
v___x_3447_ = 34;
v___x_3448_ = lean_uint32_dec_eq(v_c_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v_i_3449_; uint8_t v___x_3450_; 
v_i_3449_ = lean_string_utf8_next(v_s_3443_, v_i_3444_);
lean_dec(v_i_3444_);
v___x_3450_ = lean_string_utf8_at_end(v_s_3443_, v_i_3449_);
if (v___x_3450_ == 0)
{
uint32_t v___x_3451_; uint8_t v___x_3452_; 
v___x_3451_ = 92;
v___x_3452_ = lean_uint32_dec_eq(v_c_3446_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_string_push(v_acc_3445_, v_c_3446_);
v_i_3444_ = v_i_3449_;
v_acc_3445_ = v___x_3453_;
goto _start;
}
else
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Lean_Syntax_decodeQuotedChar(v_s_3443_, v_i_3449_);
if (lean_obj_tag(v___x_3455_) == 1)
{
lean_object* v_val_3456_; lean_object* v_fst_3457_; lean_object* v_snd_3458_; uint32_t v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v_i_3449_);
v_val_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v_fst_3457_ = lean_ctor_get(v_val_3456_, 0);
lean_inc(v_fst_3457_);
v_snd_3458_ = lean_ctor_get(v_val_3456_, 1);
lean_inc(v_snd_3458_);
lean_dec(v_val_3456_);
v___x_3459_ = lean_unbox_uint32(v_fst_3457_);
lean_dec(v_fst_3457_);
v___x_3460_ = lean_string_push(v_acc_3445_, v___x_3459_);
v_i_3444_ = v_snd_3458_;
v_acc_3445_ = v___x_3460_;
goto _start;
}
else
{
lean_object* v___x_3462_; 
lean_dec(v___x_3455_);
lean_inc_ref(v_s_3443_);
v___x_3462_ = l_Lean_Syntax_decodeStringGap(v_s_3443_, v_i_3449_);
lean_dec(v_i_3449_);
if (lean_obj_tag(v___x_3462_) == 1)
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3462_, 1);
v_i_3444_ = v_val_3463_;
goto _start;
}
else
{
lean_object* v___x_3465_; 
lean_dec(v___x_3462_);
lean_dec_ref(v_acc_3445_);
lean_dec_ref(v_s_3443_);
v___x_3465_ = lean_box(0);
return v___x_3465_;
}
}
}
}
else
{
lean_object* v___x_3466_; 
lean_dec(v_i_3449_);
lean_dec_ref(v_acc_3445_);
lean_dec_ref(v_s_3443_);
v___x_3466_ = lean_box(0);
return v___x_3466_;
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v_i_3444_);
lean_dec_ref(v_s_3443_);
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_acc_3445_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3468_, lean_object* v_i_3469_, lean_object* v_num_3470_){
_start:
{
uint32_t v_c_3471_; lean_object* v_i_3472_; uint32_t v___x_3473_; uint8_t v___x_3474_; 
v_c_3471_ = lean_string_utf8_get(v_s_3468_, v_i_3469_);
v_i_3472_ = lean_string_utf8_next(v_s_3468_, v_i_3469_);
lean_dec(v_i_3469_);
v___x_3473_ = 35;
v___x_3474_ = lean_uint32_dec_eq(v_c_3471_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3475_ = lean_string_utf8_byte_size(v_s_3468_);
v___x_3476_ = lean_unsigned_to_nat(1u);
v___x_3477_ = lean_nat_add(v_num_3470_, v___x_3476_);
lean_dec(v_num_3470_);
v___x_3478_ = lean_nat_sub(v___x_3475_, v___x_3477_);
lean_dec(v___x_3477_);
v___x_3479_ = lean_string_utf8_extract(v_s_3468_, v_i_3472_, v___x_3478_);
lean_dec(v___x_3478_);
lean_dec(v_i_3472_);
return v___x_3479_;
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_unsigned_to_nat(1u);
v___x_3481_ = lean_nat_add(v_num_3470_, v___x_3480_);
lean_dec(v_num_3470_);
v_i_3469_ = v_i_3472_;
v_num_3470_ = v___x_3481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3483_, lean_object* v_i_3484_, lean_object* v_num_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3483_, v_i_3484_, v_num_3485_);
lean_dec_ref(v_s_3483_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3487_){
_start:
{
lean_object* v___x_3488_; uint32_t v___x_3489_; uint32_t v___x_3490_; uint8_t v___x_3491_; 
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = lean_string_utf8_get(v_s_3487_, v___x_3488_);
v___x_3490_ = 114;
v___x_3491_ = lean_uint32_dec_eq(v___x_3489_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3494_ = l_Lean_Syntax_decodeStrLitAux(v_s_3487_, v___x_3492_, v___x_3493_);
return v___x_3494_;
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = lean_unsigned_to_nat(1u);
v___x_3496_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3487_, v___x_3495_, v___x_3488_);
lean_dec_ref(v_s_3487_);
v___x_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3498_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3500_ = l_Lean_Syntax_isLit_x3f(v___x_3499_, v_stx_3498_);
if (lean_obj_tag(v___x_3500_) == 1)
{
lean_object* v_val_3501_; lean_object* v___x_3502_; 
v_val_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_val_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Syntax_decodeStrLit(v_val_3501_);
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; 
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3504_);
lean_dec(v_stx_3504_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3506_){
_start:
{
lean_object* v___x_3507_; uint32_t v_c_3508_; uint32_t v___x_3509_; uint8_t v___x_3510_; 
v___x_3507_ = lean_unsigned_to_nat(1u);
v_c_3508_ = lean_string_utf8_get(v_s_3506_, v___x_3507_);
v___x_3509_ = 92;
v___x_3510_ = lean_uint32_dec_eq(v_c_3508_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_box_uint32(v_c_3508_);
v___x_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_unsigned_to_nat(2u);
v___x_3514_ = l_Lean_Syntax_decodeQuotedChar(v_s_3506_, v___x_3513_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_box(0);
return v___x_3515_;
}
else
{
lean_object* v_val_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3524_; 
v_val_3516_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3518_ = v___x_3514_;
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_val_3516_);
lean_dec(v___x_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v_fst_3520_; lean_object* v___x_3522_; 
v_fst_3520_ = lean_ctor_get(v_val_3516_, 0);
lean_inc(v_fst_3520_);
lean_dec(v_val_3516_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_fst_3520_);
v___x_3522_ = v___x_3518_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_fst_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Syntax_decodeCharLit(v_s_3525_);
lean_dec_ref(v_s_3525_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3529_ = l_Lean_Syntax_isLit_x3f(v___x_3528_, v_stx_3527_);
if (lean_obj_tag(v___x_3529_) == 1)
{
lean_object* v_val_3530_; lean_object* v___x_3531_; 
v_val_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_val_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v___x_3531_ = l_Lean_Syntax_decodeCharLit(v_val_3530_);
lean_dec(v_val_3530_);
return v___x_3531_;
}
else
{
lean_object* v___x_3532_; 
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
return v___x_3532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3533_);
lean_dec(v_stx_3533_);
return v_res_3534_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3535_){
_start:
{
uint8_t v___y_3553_; uint32_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = 65;
v___x_3559_ = lean_uint32_dec_le(v___x_3558_, v___y_3535_);
if (v___x_3559_ == 0)
{
v___y_3553_ = v___x_3559_;
goto v___jp_3552_;
}
else
{
uint32_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = 90;
v___x_3561_ = lean_uint32_dec_le(v___y_3535_, v___x_3560_);
v___y_3553_ = v___x_3561_;
goto v___jp_3552_;
}
v___jp_3536_:
{
uint32_t v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = 95;
v___x_3538_ = lean_uint32_dec_eq(v___y_3535_, v___x_3537_);
if (v___x_3538_ == 0)
{
uint32_t v___x_3539_; uint8_t v___x_3540_; 
v___x_3539_ = 39;
v___x_3540_ = lean_uint32_dec_eq(v___y_3535_, v___x_3539_);
if (v___x_3540_ == 0)
{
uint32_t v___x_3541_; uint8_t v___x_3542_; 
v___x_3541_ = 33;
v___x_3542_ = lean_uint32_dec_eq(v___y_3535_, v___x_3541_);
if (v___x_3542_ == 0)
{
uint32_t v___x_3543_; uint8_t v___x_3544_; 
v___x_3543_ = 63;
v___x_3544_ = lean_uint32_dec_eq(v___y_3535_, v___x_3543_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
v___x_3545_ = l_Lean_isLetterLike(v___y_3535_);
if (v___x_3545_ == 0)
{
uint8_t v___x_3546_; 
v___x_3546_ = l_Lean_isSubScriptAlnum(v___y_3535_);
return v___x_3546_;
}
else
{
return v___x_3545_;
}
}
else
{
return v___x_3544_;
}
}
else
{
return v___x_3542_;
}
}
else
{
return v___x_3540_;
}
}
else
{
return v___x_3538_;
}
}
v___jp_3547_:
{
uint32_t v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = 48;
v___x_3549_ = lean_uint32_dec_le(v___x_3548_, v___y_3535_);
if (v___x_3549_ == 0)
{
goto v___jp_3536_;
}
else
{
uint32_t v___x_3550_; uint8_t v___x_3551_; 
v___x_3550_ = 57;
v___x_3551_ = lean_uint32_dec_le(v___y_3535_, v___x_3550_);
if (v___x_3551_ == 0)
{
goto v___jp_3536_;
}
else
{
return v___x_3551_;
}
}
}
v___jp_3552_:
{
if (v___y_3553_ == 0)
{
uint32_t v___x_3554_; uint8_t v___x_3555_; 
v___x_3554_ = 97;
v___x_3555_ = lean_uint32_dec_le(v___x_3554_, v___y_3535_);
if (v___x_3555_ == 0)
{
goto v___jp_3547_;
}
else
{
uint32_t v___x_3556_; uint8_t v___x_3557_; 
v___x_3556_ = 122;
v___x_3557_ = lean_uint32_dec_le(v___y_3535_, v___x_3556_);
if (v___x_3557_ == 0)
{
goto v___jp_3547_;
}
else
{
return v___x_3557_;
}
}
}
else
{
return v___y_3553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3562_){
_start:
{
uint32_t v___y_509__boxed_3563_; uint8_t v_res_3564_; lean_object* v_r_3565_; 
v___y_509__boxed_3563_ = lean_unbox_uint32(v___y_3562_);
lean_dec(v___y_3562_);
v_res_3564_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_509__boxed_3563_);
v_r_3565_ = lean_box(v_res_3564_);
return v_r_3565_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3566_, uint32_t v___x_3567_, uint32_t v___y_3568_){
_start:
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_uint32_dec_le(v___x_3566_, v___y_3568_);
if (v___x_3569_ == 0)
{
return v___x_3569_;
}
else
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_uint32_dec_le(v___y_3568_, v___x_3567_);
return v___x_3570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3571_, lean_object* v___x_3572_, lean_object* v___y_3573_){
_start:
{
uint32_t v___x_564__boxed_3574_; uint32_t v___x_565__boxed_3575_; uint32_t v___y_566__boxed_3576_; uint8_t v_res_3577_; lean_object* v_r_3578_; 
v___x_564__boxed_3574_ = lean_unbox_uint32(v___x_3571_);
lean_dec(v___x_3571_);
v___x_565__boxed_3575_ = lean_unbox_uint32(v___x_3572_);
lean_dec(v___x_3572_);
v___y_566__boxed_3576_ = lean_unbox_uint32(v___y_3573_);
lean_dec(v___y_3573_);
v_res_3577_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_564__boxed_3574_, v___x_565__boxed_3575_, v___y_566__boxed_3576_);
v_r_3578_ = lean_box(v_res_3577_);
return v_r_3578_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3579_, uint8_t v___x_3580_, uint32_t v_x_3581_){
_start:
{
uint32_t v___x_3582_; uint8_t v___x_3583_; 
v___x_3582_ = 187;
v___x_3583_ = lean_uint32_dec_eq(v_x_3581_, v___x_3582_);
if (v___x_3583_ == 0)
{
return v___x_3579_;
}
else
{
return v___x_3580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3584_, lean_object* v___x_3585_, lean_object* v_x_3586_){
_start:
{
uint8_t v___x_577__boxed_3587_; uint8_t v___x_578__boxed_3588_; uint32_t v_x_579__boxed_3589_; uint8_t v_res_3590_; lean_object* v_r_3591_; 
v___x_577__boxed_3587_ = lean_unbox(v___x_3584_);
v___x_578__boxed_3588_ = lean_unbox(v___x_3585_);
v_x_579__boxed_3589_ = lean_unbox_uint32(v_x_3586_);
lean_dec(v_x_3586_);
v_res_3590_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_577__boxed_3587_, v___x_578__boxed_3588_, v_x_579__boxed_3589_);
v_r_3591_ = lean_box(v_res_3590_);
return v_r_3591_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = 48;
v___x_3594_ = lean_box_uint32(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = 57;
v___x_3596_ = lean_box_uint32(v___x_3595_);
return v___x_3596_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___f_3599_; 
v___x_3597_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3598_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3599_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3599_, 0, v___x_3597_);
lean_closure_set(v___f_3599_, 1, v___x_3598_);
return v___f_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3600_, lean_object* v_acc_3601_){
_start:
{
lean_object* v_ss_3603_; lean_object* v_acc_3604_; uint8_t v___x_3613_; 
lean_inc_ref(v_ss_3600_);
v___x_3613_ = lean_substring_isempty(v_ss_3600_);
if (v___x_3613_ == 0)
{
uint32_t v_curr_3614_; uint32_t v___x_3615_; uint8_t v___x_3616_; 
lean_inc_ref(v_ss_3600_);
v_curr_3614_ = lean_substring_front(v_ss_3600_);
v___x_3615_ = 171;
v___x_3616_ = lean_uint32_dec_eq(v_curr_3614_, v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___f_3617_; uint8_t v___y_3649_; uint32_t v___x_3654_; uint8_t v___x_3655_; 
v___f_3617_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3654_ = 65;
v___x_3655_ = lean_uint32_dec_le(v___x_3654_, v_curr_3614_);
if (v___x_3655_ == 0)
{
v___y_3649_ = v___x_3655_;
goto v___jp_3648_;
}
else
{
uint32_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3656_ = 90;
v___x_3657_ = lean_uint32_dec_le(v_curr_3614_, v___x_3656_);
v___y_3649_ = v___x_3657_;
goto v___jp_3648_;
}
v___jp_3618_:
{
lean_object* v_idPart_3619_; lean_object* v_startPos_3620_; lean_object* v_stopPos_3621_; lean_object* v_startPos_3622_; lean_object* v_stopPos_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_inc_ref(v_ss_3600_);
v_idPart_3619_ = lean_substring_takewhile(v_ss_3600_, v___f_3617_);
v_startPos_3620_ = lean_ctor_get(v_idPart_3619_, 1);
lean_inc(v_startPos_3620_);
v_stopPos_3621_ = lean_ctor_get(v_idPart_3619_, 2);
lean_inc(v_stopPos_3621_);
v_startPos_3622_ = lean_ctor_get(v_ss_3600_, 1);
v_stopPos_3623_ = lean_ctor_get(v_ss_3600_, 2);
v___x_3624_ = lean_nat_sub(v_stopPos_3621_, v_startPos_3620_);
lean_dec(v_startPos_3620_);
lean_dec(v_stopPos_3621_);
v___x_3625_ = lean_nat_sub(v_stopPos_3623_, v_startPos_3622_);
v___x_3626_ = lean_substring_extract(v_ss_3600_, v___x_3624_, v___x_3625_);
v___x_3627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_idPart_3619_);
lean_ctor_set(v___x_3627_, 1, v_acc_3601_);
v_ss_3603_ = v___x_3626_;
v_acc_3604_ = v___x_3627_;
goto v___jp_3602_;
}
v___jp_3628_:
{
uint32_t v___x_3629_; uint8_t v___x_3630_; 
v___x_3629_ = 95;
v___x_3630_ = lean_uint32_dec_eq(v_curr_3614_, v___x_3629_);
if (v___x_3630_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = l_Lean_isLetterLike(v_curr_3614_);
if (v___x_3631_ == 0)
{
uint32_t v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = 48;
v___x_3633_ = lean_uint32_dec_le(v___x_3632_, v_curr_3614_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; 
lean_dec(v_acc_3601_);
lean_dec_ref(v_ss_3600_);
v___x_3634_ = lean_box(0);
return v___x_3634_;
}
else
{
uint32_t v___x_3635_; uint8_t v___x_3636_; 
v___x_3635_ = 57;
v___x_3636_ = lean_uint32_dec_le(v_curr_3614_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec(v_acc_3601_);
lean_dec_ref(v_ss_3600_);
v___x_3637_ = lean_box(0);
return v___x_3637_;
}
else
{
lean_object* v___f_3638_; lean_object* v_idPart_3639_; lean_object* v_startPos_3640_; lean_object* v_stopPos_3641_; lean_object* v_startPos_3642_; lean_object* v_stopPos_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___f_3638_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3600_);
v_idPart_3639_ = lean_substring_takewhile(v_ss_3600_, v___f_3638_);
v_startPos_3640_ = lean_ctor_get(v_idPart_3639_, 1);
lean_inc(v_startPos_3640_);
v_stopPos_3641_ = lean_ctor_get(v_idPart_3639_, 2);
lean_inc(v_stopPos_3641_);
v_startPos_3642_ = lean_ctor_get(v_ss_3600_, 1);
v_stopPos_3643_ = lean_ctor_get(v_ss_3600_, 2);
v___x_3644_ = lean_nat_sub(v_stopPos_3641_, v_startPos_3640_);
lean_dec(v_startPos_3640_);
lean_dec(v_stopPos_3641_);
v___x_3645_ = lean_nat_sub(v_stopPos_3643_, v_startPos_3642_);
v___x_3646_ = lean_substring_extract(v_ss_3600_, v___x_3644_, v___x_3645_);
v___x_3647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3647_, 0, v_idPart_3639_);
lean_ctor_set(v___x_3647_, 1, v_acc_3601_);
v_ss_3603_ = v___x_3646_;
v_acc_3604_ = v___x_3647_;
goto v___jp_3602_;
}
}
}
else
{
goto v___jp_3618_;
}
}
else
{
goto v___jp_3618_;
}
}
v___jp_3648_:
{
if (v___y_3649_ == 0)
{
uint32_t v___x_3650_; uint8_t v___x_3651_; 
v___x_3650_ = 97;
v___x_3651_ = lean_uint32_dec_le(v___x_3650_, v_curr_3614_);
if (v___x_3651_ == 0)
{
goto v___jp_3628_;
}
else
{
uint32_t v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = 122;
v___x_3653_ = lean_uint32_dec_le(v_curr_3614_, v___x_3652_);
if (v___x_3653_ == 0)
{
goto v___jp_3628_;
}
else
{
goto v___jp_3618_;
}
}
}
else
{
goto v___jp_3618_;
}
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___f_3660_; lean_object* v_escapedPart_3661_; lean_object* v_str_3662_; lean_object* v_startPos_3663_; lean_object* v_stopPos_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3685_; 
v___x_3658_ = lean_box(v___x_3616_);
v___x_3659_ = lean_box(v___x_3613_);
v___f_3660_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3660_, 0, v___x_3658_);
lean_closure_set(v___f_3660_, 1, v___x_3659_);
lean_inc_ref(v_ss_3600_);
v_escapedPart_3661_ = lean_substring_takewhile(v_ss_3600_, v___f_3660_);
v_str_3662_ = lean_ctor_get(v_escapedPart_3661_, 0);
v_startPos_3663_ = lean_ctor_get(v_escapedPart_3661_, 1);
v_stopPos_3664_ = lean_ctor_get(v_escapedPart_3661_, 2);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_escapedPart_3661_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3666_ = v_escapedPart_3661_;
v_isShared_3667_ = v_isSharedCheck_3685_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_stopPos_3664_);
lean_inc(v_startPos_3663_);
lean_inc(v_str_3662_);
lean_dec(v_escapedPart_3661_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3685_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v_startPos_3668_; lean_object* v_stopPos_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_escapedPart_3673_; 
v_startPos_3668_ = lean_ctor_get(v_ss_3600_, 1);
v_stopPos_3669_ = lean_ctor_get(v_ss_3600_, 2);
v___x_3670_ = lean_string_utf8_next(v_str_3662_, v_stopPos_3664_);
lean_dec(v_stopPos_3664_);
lean_inc(v_stopPos_3669_);
v___x_3671_ = lean_string_pos_min(v_stopPos_3669_, v___x_3670_);
lean_inc(v___x_3671_);
lean_inc(v_startPos_3663_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 2, v___x_3671_);
v_escapedPart_3673_ = v___x_3666_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_str_3662_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_startPos_3663_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v___x_3671_);
v_escapedPart_3673_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; uint32_t v___x_3676_; uint32_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3674_ = lean_nat_sub(v___x_3671_, v_startPos_3663_);
lean_dec(v_startPos_3663_);
lean_dec(v___x_3671_);
lean_inc(v___x_3674_);
lean_inc_ref_n(v_escapedPart_3673_, 2);
v___x_3675_ = lean_substring_prev(v_escapedPart_3673_, v___x_3674_);
v___x_3676_ = lean_substring_get(v_escapedPart_3673_, v___x_3675_);
v___x_3677_ = 187;
v___x_3678_ = lean_uint32_dec_eq(v___x_3676_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; 
lean_dec(v___x_3674_);
lean_dec_ref(v_escapedPart_3673_);
lean_dec(v_acc_3601_);
lean_dec_ref(v_ss_3600_);
v___x_3679_ = lean_box(0);
return v___x_3679_;
}
else
{
if (v___x_3613_ == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_nat_sub(v_stopPos_3669_, v_startPos_3668_);
v___x_3681_ = lean_substring_extract(v_ss_3600_, v___x_3674_, v___x_3680_);
v___x_3682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3682_, 0, v_escapedPart_3673_);
lean_ctor_set(v___x_3682_, 1, v_acc_3601_);
v_ss_3603_ = v___x_3681_;
v_acc_3604_ = v___x_3682_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3683_; 
lean_dec(v___x_3674_);
lean_dec_ref(v_escapedPart_3673_);
lean_dec(v_acc_3601_);
lean_dec_ref(v_ss_3600_);
v___x_3683_ = lean_box(0);
return v___x_3683_;
}
}
}
}
}
}
else
{
lean_object* v___x_3686_; 
lean_dec(v_acc_3601_);
lean_dec_ref(v_ss_3600_);
v___x_3686_ = lean_box(0);
return v___x_3686_;
}
v___jp_3602_:
{
uint32_t v___x_3605_; uint32_t v___x_3606_; uint8_t v___x_3607_; 
lean_inc_ref(v_ss_3603_);
v___x_3605_ = lean_substring_front(v_ss_3603_);
v___x_3606_ = 46;
v___x_3607_ = lean_uint32_dec_eq(v___x_3605_, v___x_3606_);
if (v___x_3607_ == 0)
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_substring_isempty(v_ss_3603_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
lean_dec(v_acc_3604_);
v___x_3609_ = lean_box(0);
return v___x_3609_;
}
else
{
return v_acc_3604_;
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = lean_unsigned_to_nat(1u);
v___x_3611_ = lean_substring_drop(v_ss_3603_, v___x_3610_);
v_ss_3600_ = v___x_3611_;
v_acc_3601_ = v_acc_3604_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3688_ = lean_box(0);
v___x_3689_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3687_, v___x_3688_);
v___x_3690_ = l_List_reverse___redArg(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3694_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3695_ = lean_unsigned_to_nat(10u);
v___x_3696_ = lean_unsigned_to_nat(1237u);
v___x_3697_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3698_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3699_ = l_mkPanicMessageWithDecl(v___x_3698_, v___x_3697_, v___x_3696_, v___x_3695_, v___x_3694_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3700_, lean_object* v_x_3701_){
_start:
{
if (lean_obj_tag(v_x_3701_) == 0)
{
lean_inc(v_init_3700_);
return v_init_3700_;
}
else
{
lean_object* v_head_3702_; lean_object* v_tail_3703_; lean_object* v___x_3704_; lean_object* v_comp_3705_; uint32_t v___x_3706_; uint32_t v___x_3707_; uint8_t v___x_3708_; 
v_head_3702_ = lean_ctor_get(v_x_3701_, 0);
lean_inc(v_head_3702_);
v_tail_3703_ = lean_ctor_get(v_x_3701_, 1);
lean_inc(v_tail_3703_);
lean_dec_ref_known(v_x_3701_, 2);
v___x_3704_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3700_, v_tail_3703_);
v_comp_3705_ = lean_substring_tostring(v_head_3702_);
lean_inc_ref(v_comp_3705_);
v___x_3706_ = lean_string_front(v_comp_3705_);
v___x_3707_ = 171;
v___x_3708_ = lean_uint32_dec_eq(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
uint32_t v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = 48;
v___x_3710_ = lean_uint32_dec_le(v___x_3709_, v___x_3706_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Name_str___override(v___x_3704_, v_comp_3705_);
return v___x_3711_;
}
else
{
uint32_t v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = 57;
v___x_3713_ = lean_uint32_dec_le(v___x_3706_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_Name_str___override(v___x_3704_, v_comp_3705_);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3705_);
lean_dec_ref(v_comp_3705_);
if (lean_obj_tag(v___x_3715_) == 1)
{
lean_object* v_val_3716_; lean_object* v___x_3717_; 
v_val_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_val_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_Name_num___override(v___x_3704_, v_val_3716_);
return v___x_3717_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_dec(v___x_3715_);
lean_dec(v___x_3704_);
v___x_3718_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3719_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3718_);
return v___x_3719_;
}
}
}
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3721_ = lean_string_drop(v_comp_3705_, v___x_3720_);
v___x_3722_ = lean_string_dropright(v___x_3721_, v___x_3720_);
v___x_3723_ = l_Lean_Name_str___override(v___x_3704_, v___x_3722_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3724_, lean_object* v_x_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3724_, v_x_3725_);
lean_dec(v_init_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3727_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_box(0);
v___x_3729_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3727_, v___x_3728_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_box(0);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_box(0);
v___x_3732_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3731_, v___x_3729_);
return v___x_3732_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3733_){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3734_ = lean_unsigned_to_nat(0u);
v___x_3735_ = lean_string_utf8_byte_size(v_s_3733_);
v___x_3736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3736_, 0, v_s_3733_);
lean_ctor_set(v___x_3736_, 1, v___x_3734_);
lean_ctor_set(v___x_3736_, 2, v___x_3735_);
v___x_3737_ = l_Substring_Raw_toName(v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3738_){
_start:
{
lean_object* v___x_3739_; uint32_t v___x_3740_; uint32_t v___x_3741_; uint8_t v___x_3742_; 
v___x_3739_ = lean_unsigned_to_nat(0u);
v___x_3740_ = lean_string_utf8_get(v_s_3738_, v___x_3739_);
v___x_3741_ = 96;
v___x_3742_ = lean_uint32_dec_eq(v___x_3740_, v___x_3741_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; 
lean_dec_ref(v_s_3738_);
v___x_3743_ = lean_box(0);
return v___x_3743_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3744_ = lean_string_utf8_byte_size(v_s_3738_);
v___x_3745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3745_, 0, v_s_3738_);
lean_ctor_set(v___x_3745_, 1, v___x_3739_);
lean_ctor_set(v___x_3745_, 2, v___x_3744_);
v___x_3746_ = lean_unsigned_to_nat(1u);
v___x_3747_ = lean_substring_drop(v___x_3745_, v___x_3746_);
v___x_3748_ = l_Substring_Raw_toName(v___x_3747_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_box(0);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
return v___x_3750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3751_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3753_ = l_Lean_Syntax_isLit_x3f(v___x_3752_, v_stx_3751_);
if (lean_obj_tag(v___x_3753_) == 1)
{
lean_object* v_val_3754_; lean_object* v___x_3755_; 
v_val_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_val_3754_);
lean_dec_ref_known(v___x_3753_, 1);
v___x_3755_ = l_Lean_Syntax_decodeNameLit(v_val_3754_);
return v___x_3755_;
}
else
{
lean_object* v___x_3756_; 
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(0);
return v___x_3756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3757_);
lean_dec(v_stx_3757_);
return v_res_3758_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3759_){
_start:
{
if (lean_obj_tag(v_x_3759_) == 1)
{
lean_object* v_args_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v_args_3760_ = lean_ctor_get(v_x_3759_, 2);
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_array_get_size(v_args_3760_);
v___x_3763_ = lean_nat_dec_lt(v___x_3761_, v___x_3762_);
return v___x_3763_;
}
else
{
uint8_t v___x_3764_; 
v___x_3764_ = 0;
return v___x_3764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3765_){
_start:
{
uint8_t v_res_3766_; lean_object* v_r_3767_; 
v_res_3766_ = l_Lean_Syntax_hasArgs(v_x_3765_);
lean_dec(v_x_3765_);
v_r_3767_ = lean_box(v_res_3766_);
return v_r_3767_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3768_){
_start:
{
if (lean_obj_tag(v_x_3768_) == 2)
{
uint8_t v___x_3769_; 
v___x_3769_ = 1;
return v___x_3769_;
}
else
{
uint8_t v___x_3770_; 
v___x_3770_ = 0;
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3771_){
_start:
{
uint8_t v_res_3772_; lean_object* v_r_3773_; 
v_res_3772_ = l_Lean_Syntax_isAtom(v_x_3771_);
lean_dec(v_x_3771_);
v_r_3773_ = lean_box(v_res_3772_);
return v_r_3773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3774_, lean_object* v_x_3775_){
_start:
{
if (lean_obj_tag(v_x_3775_) == 2)
{
lean_object* v_val_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v_val_3776_ = lean_ctor_get(v_x_3775_, 1);
lean_inc_ref(v_val_3776_);
lean_dec_ref_known(v_x_3775_, 2);
v___x_3777_ = lean_string_trim(v_val_3776_);
v___x_3778_ = lean_string_trim(v_token_3774_);
v___x_3779_ = lean_string_dec_eq(v___x_3777_, v___x_3778_);
lean_dec_ref(v___x_3778_);
lean_dec_ref(v___x_3777_);
return v___x_3779_;
}
else
{
uint8_t v___x_3780_; 
lean_dec(v_x_3775_);
lean_dec_ref(v_token_3774_);
v___x_3780_ = 0;
return v___x_3780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3781_, lean_object* v_x_3782_){
_start:
{
uint8_t v_res_3783_; lean_object* v_r_3784_; 
v_res_3783_ = l_Lean_Syntax_isToken(v_token_3781_, v_x_3782_);
v_r_3784_ = lean_box(v_res_3783_);
return v_r_3784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3785_){
_start:
{
switch(lean_obj_tag(v_stx_3785_))
{
case 1:
{
lean_object* v_kind_3786_; lean_object* v_args_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_kind_3786_ = lean_ctor_get(v_stx_3785_, 1);
v_args_3787_ = lean_ctor_get(v_stx_3785_, 2);
v___x_3788_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3789_ = lean_name_eq(v_kind_3786_, v___x_3788_);
if (v___x_3789_ == 0)
{
return v___x_3789_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = lean_array_get_size(v_args_3787_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = lean_nat_dec_eq(v___x_3790_, v___x_3791_);
return v___x_3792_;
}
}
case 0:
{
uint8_t v___x_3793_; 
v___x_3793_ = 1;
return v___x_3793_;
}
default: 
{
uint8_t v___x_3794_; 
v___x_3794_ = 0;
return v___x_3794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3795_){
_start:
{
uint8_t v_res_3796_; lean_object* v_r_3797_; 
v_res_3796_ = l_Lean_Syntax_isNone(v_stx_3795_);
lean_dec(v_stx_3795_);
v_r_3797_ = lean_box(v_res_3796_);
return v_r_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Syntax_getOptional_x3f(v_stx_3798_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_box(0);
return v___x_3800_;
}
else
{
lean_object* v_val_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3809_; 
v_val_3801_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3803_ = v___x_3799_;
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_val_3801_);
lean_dec(v___x_3799_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = l_Lean_Syntax_getId(v_val_3801_);
lean_dec(v_val_3801_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3805_);
v___x_3807_ = v___x_3803_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3810_);
lean_dec(v_stx_3810_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3812_, lean_object* v_x_3813_){
_start:
{
if (lean_obj_tag(v_x_3813_) == 1)
{
lean_object* v_args_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_args_3814_ = lean_ctor_get(v_x_3813_, 2);
lean_inc_ref(v_p_3812_);
lean_inc_ref(v_x_3813_);
v___x_3815_ = lean_apply_1(v_p_3812_, v_x_3813_);
v___x_3816_ = lean_unbox(v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; size_t v_sz_3819_; size_t v___x_3820_; lean_object* v___x_3821_; lean_object* v_fst_3822_; 
lean_inc_ref(v_args_3814_);
lean_dec_ref_known(v_x_3813_, 3);
v___x_3817_ = lean_box(0);
v___x_3818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3819_ = lean_array_size(v_args_3814_);
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3812_, v_args_3814_, v_sz_3819_, v___x_3820_, v___x_3818_);
lean_dec_ref(v_args_3814_);
v_fst_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_fst_3822_);
lean_dec_ref(v___x_3821_);
if (lean_obj_tag(v_fst_3822_) == 0)
{
return v___x_3817_;
}
else
{
lean_object* v_val_3823_; 
v_val_3823_ = lean_ctor_get(v_fst_3822_, 0);
lean_inc(v_val_3823_);
lean_dec_ref_known(v_fst_3822_, 1);
return v_val_3823_;
}
}
else
{
lean_object* v___x_3824_; 
lean_dec_ref(v_p_3812_);
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_x_3813_);
return v___x_3824_;
}
}
else
{
lean_object* v___x_3825_; uint8_t v___x_3826_; 
lean_inc(v_x_3813_);
v___x_3825_ = lean_apply_1(v_p_3812_, v_x_3813_);
v___x_3826_ = lean_unbox(v___x_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; 
lean_dec(v_x_3813_);
v___x_3827_ = lean_box(0);
return v___x_3827_;
}
else
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_x_3813_);
return v___x_3828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3829_, lean_object* v_as_3830_, size_t v_sz_3831_, size_t v_i_3832_, lean_object* v_b_3833_){
_start:
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_usize_dec_lt(v_i_3832_, v_sz_3831_);
if (v___x_3834_ == 0)
{
lean_dec_ref(v_p_3829_);
lean_inc_ref(v_b_3833_);
return v_b_3833_;
}
else
{
lean_object* v___x_3835_; lean_object* v_a_3836_; lean_object* v___x_3837_; 
v___x_3835_ = lean_box(0);
v_a_3836_ = lean_array_uget_borrowed(v_as_3830_, v_i_3832_);
lean_inc(v_a_3836_);
lean_inc_ref(v_p_3829_);
v___x_3837_ = l_Lean_Syntax_findAux(v_p_3829_, v_a_3836_);
if (lean_obj_tag(v___x_3837_) == 1)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec_ref(v_p_3829_);
v___x_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
v___x_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
lean_ctor_set(v___x_3839_, 1, v___x_3835_);
return v___x_3839_;
}
else
{
lean_object* v___x_3840_; size_t v___x_3841_; size_t v___x_3842_; 
lean_dec(v___x_3837_);
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3841_ = ((size_t)1ULL);
v___x_3842_ = lean_usize_add(v_i_3832_, v___x_3841_);
v_i_3832_ = v___x_3842_;
v_b_3833_ = v___x_3840_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3844_, lean_object* v_as_3845_, lean_object* v_sz_3846_, lean_object* v_i_3847_, lean_object* v_b_3848_){
_start:
{
size_t v_sz_boxed_3849_; size_t v_i_boxed_3850_; lean_object* v_res_3851_; 
v_sz_boxed_3849_ = lean_unbox_usize(v_sz_3846_);
lean_dec(v_sz_3846_);
v_i_boxed_3850_ = lean_unbox_usize(v_i_3847_);
lean_dec(v_i_3847_);
v_res_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3844_, v_as_3845_, v_sz_boxed_3849_, v_i_boxed_3850_, v_b_3848_);
lean_dec_ref(v_b_3848_);
lean_dec_ref(v_as_3845_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3852_, lean_object* v_p_3853_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Syntax_findAux(v_p_3853_, v_stx_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Lean_Syntax_isNatLit_x3f(v_s_3855_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_unsigned_to_nat(0u);
return v___x_3857_;
}
else
{
lean_object* v_val_3858_; 
v_val_3858_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_val_3858_);
lean_dec_ref_known(v___x_3856_, 1);
return v_val_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_TSyntax_getNat(v_s_3859_);
lean_dec(v_s_3859_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3864_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3866_ = l_Lean_Syntax_isLit_x3f(v___x_3865_, v_stx_3864_);
if (lean_obj_tag(v___x_3866_) == 1)
{
lean_object* v_val_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_val_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3867_, v___x_3868_, v___x_3868_);
lean_dec(v_val_3867_);
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; 
lean_dec(v___x_3866_);
v___x_3870_ = lean_box(0);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3871_);
lean_dec(v_stx_3871_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3873_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_unsigned_to_nat(0u);
return v___x_3875_;
}
else
{
lean_object* v_val_3876_; 
v_val_3876_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_val_3876_);
lean_dec_ref_known(v___x_3874_, 1);
return v_val_3876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_TSyntax_getHexNumVal(v_s_3877_);
lean_dec(v_s_3877_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3879_, lean_object* v_p_3880_, lean_object* v_n_3881_){
_start:
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_string_utf8_at_end(v_s_3879_, v_p_3880_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; uint32_t v___x_3884_; uint32_t v___x_3885_; uint8_t v___x_3886_; 
v___x_3883_ = lean_string_utf8_next(v_s_3879_, v_p_3880_);
v___x_3884_ = lean_string_utf8_get(v_s_3879_, v_p_3880_);
lean_dec(v_p_3880_);
v___x_3885_ = 95;
v___x_3886_ = lean_uint32_dec_eq(v___x_3884_, v___x_3885_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_unsigned_to_nat(1u);
v___x_3888_ = lean_nat_add(v_n_3881_, v___x_3887_);
lean_dec(v_n_3881_);
v_p_3880_ = v___x_3883_;
v_n_3881_ = v___x_3888_;
goto _start;
}
else
{
v_p_3880_ = v___x_3883_;
goto _start;
}
}
else
{
lean_dec(v_p_3880_);
return v_n_3881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3891_, lean_object* v_p_3892_, lean_object* v_n_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3891_, v_p_3892_, v_n_3893_);
lean_dec_ref(v_s_3891_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3895_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3897_ = l_Lean_Syntax_isLit_x3f(v___x_3896_, v_s_3895_);
if (lean_obj_tag(v___x_3897_) == 1)
{
lean_object* v_val_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_val_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3898_, v___x_3899_, v___x_3899_);
lean_dec(v_val_3898_);
return v___x_3900_;
}
else
{
lean_object* v___x_3901_; 
lean_dec(v___x_3897_);
v___x_3901_ = lean_unsigned_to_nat(0u);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_TSyntax_getHexNumSize(v_s_3902_);
lean_dec(v_s_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3904_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Syntax_getId(v_s_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_TSyntax_getId(v_s_3906_);
lean_dec(v_s_3906_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3915_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3915_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v___x_3917_; 
v___x_3917_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3917_;
}
else
{
lean_object* v_val_3918_; 
v_val_3918_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_val_3918_);
lean_dec_ref_known(v___x_3916_, 1);
return v_val_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_TSyntax_getScientific(v_s_3919_);
lean_dec(v_s_3919_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Lean_Syntax_isStrLit_x3f(v_s_3921_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = ((lean_object*)(l_Lean_versionString___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_TSyntax_getString(v_s_3925_);
lean_dec(v_s_3925_);
return v_res_3926_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_Syntax_isCharLit_x3f(v_s_3927_);
if (lean_obj_tag(v___x_3928_) == 0)
{
uint32_t v___x_3929_; 
v___x_3929_ = 65;
return v___x_3929_;
}
else
{
lean_object* v_val_3930_; uint32_t v___x_3931_; 
v_val_3930_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3931_ = lean_unbox_uint32(v_val_3930_);
lean_dec(v_val_3930_);
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3932_){
_start:
{
uint32_t v_res_3933_; lean_object* v_r_3934_; 
v_res_3933_ = l_Lean_TSyntax_getChar(v_s_3932_);
lean_dec(v_s_3932_);
v_r_3934_ = lean_box_uint32(v_res_3933_);
return v_r_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_Syntax_isNameLit_x3f(v_s_3935_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_box(0);
return v___x_3937_;
}
else
{
lean_object* v_val_3938_; 
v_val_3938_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v___x_3936_, 1);
return v_val_3938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_TSyntax_getName(v_s_3939_);
lean_dec(v_s_3939_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3941_){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = lean_unsigned_to_nat(0u);
v___x_3943_ = l_Lean_Syntax_getArg(v_s_3941_, v___x_3942_);
v___x_3944_ = l_Lean_Syntax_getId(v___x_3943_);
lean_dec(v___x_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_TSyntax_getHygieneInfo(v_s_3945_);
lean_dec(v_s_3945_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3947_, v_a_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3950_, v_a_3951_);
lean_dec_ref(v_a_3951_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3953_){
_start:
{
lean_object* v___f_3954_; 
v___f_3954_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3954_, 0, v_sep_3953_);
return v___f_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3955_, lean_object* v_sep_3956_){
_start:
{
lean_object* v___f_3957_; 
v___f_3957_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3957_, 0, v_sep_3956_);
return v___f_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3958_, lean_object* v_sep_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3958_, v_sep_3959_);
lean_dec(v_k_3958_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3961_, lean_object* v_val_3962_, uint8_t v_canonical_3963_){
_start:
{
lean_object* v___x_3964_; lean_object* v_src_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v_imported_3968_; lean_object* v_ctx_3969_; lean_object* v_scopes_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3986_; 
v___x_3964_ = lean_unsigned_to_nat(0u);
v_src_3965_ = l_Lean_Syntax_getArg(v_s_3961_, v___x_3964_);
v___x_3966_ = l_Lean_Syntax_getId(v_src_3965_);
v___x_3967_ = l_Lean_extractMacroScopes(v___x_3966_);
v_imported_3968_ = lean_ctor_get(v___x_3967_, 1);
v_ctx_3969_ = lean_ctor_get(v___x_3967_, 2);
v_scopes_3970_ = lean_ctor_get(v___x_3967_, 3);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3986_ == 0)
{
lean_object* v_unused_3987_; 
v_unused_3987_ = lean_ctor_get(v___x_3967_, 0);
lean_dec(v_unused_3987_);
v___x_3972_ = v___x_3967_;
v_isShared_3973_ = v_isSharedCheck_3986_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_scopes_3970_);
lean_inc(v_ctx_3969_);
lean_inc(v_imported_3968_);
lean_dec(v___x_3967_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3986_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = l_Lean_Name_eraseMacroScopes(v_val_3962_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_imported_3968_);
lean_ctor_set(v_reuseFailAlloc_3985_, 2, v_ctx_3969_);
lean_ctor_set(v_reuseFailAlloc_3985_, 3, v_scopes_3970_);
v___x_3976_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v_id_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_id_3977_ = l_Lean_MacroScopesView_review(v___x_3976_);
v___x_3978_ = l_Lean_SourceInfo_fromRef(v_src_3965_, v_canonical_3963_);
lean_dec(v_src_3965_);
v___x_3979_ = 1;
v___x_3980_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3962_, v___x_3979_);
v___x_3981_ = lean_string_utf8_byte_size(v___x_3980_);
v___x_3982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3964_);
lean_ctor_set(v___x_3982_, 2, v___x_3981_);
v___x_3983_ = lean_box(0);
v___x_3984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3978_);
lean_ctor_set(v___x_3984_, 1, v___x_3982_);
lean_ctor_set(v___x_3984_, 2, v_id_3977_);
lean_ctor_set(v___x_3984_, 3, v___x_3983_);
return v___x_3984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_3988_, lean_object* v_val_3989_, lean_object* v_canonical_3990_){
_start:
{
uint8_t v_canonical_boxed_3991_; lean_object* v_res_3992_; 
v_canonical_boxed_3991_ = lean_unbox(v_canonical_3990_);
v_res_3992_ = l_Lean_HygieneInfo_mkIdent(v_s_3988_, v_val_3989_, v_canonical_boxed_3991_);
lean_dec(v_s_3988_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_3993_, lean_object* v_inst_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = lean_apply_1(v_inst_3993_, v_a_3995_);
v___x_3997_ = lean_apply_1(v_inst_3994_, v___x_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_3998_, lean_object* v_inst_3999_){
_start:
{
lean_object* v___f_4000_; 
v___f_4000_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4000_, 0, v_inst_3998_);
lean_closure_set(v___f_4000_, 1, v_inst_3999_);
return v___f_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4001_, lean_object* v_k_4002_, lean_object* v_k_x27_4003_, lean_object* v_inst_4004_, lean_object* v_inst_4005_){
_start:
{
lean_object* v___f_4006_; 
v___f_4006_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4006_, 0, v_inst_4004_);
lean_closure_set(v___f_4006_, 1, v_inst_4005_);
return v___f_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4007_, lean_object* v_k_4008_, lean_object* v_k_x27_4009_, lean_object* v_inst_4010_, lean_object* v_inst_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4007_, v_k_4008_, v_k_x27_4009_, v_inst_4010_, v_inst_4011_);
lean_dec(v_k_x27_4009_);
lean_dec(v_k_4008_);
return v_res_4012_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4021_ = l_Lean_mkCIdent(v___x_4020_);
return v___x_4021_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4027_ = l_Lean_mkCIdent(v___x_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4028_){
_start:
{
if (v_x_4028_ == 0)
{
lean_object* v___x_4029_; 
v___x_4029_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4029_;
}
else
{
lean_object* v___x_4030_; 
v___x_4030_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4031_){
_start:
{
uint8_t v_x_85__boxed_4032_; lean_object* v_res_4033_; 
v_x_85__boxed_4032_ = lean_unbox(v_x_4031_);
v_res_4033_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4032_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4036_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_box(2);
v___x_4038_ = l_Lean_Syntax_mkCharLit(v_val_4036_, v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4039_){
_start:
{
uint32_t v_val_boxed_4040_; lean_object* v_res_4041_; 
v_val_boxed_4040_ = lean_unbox_uint32(v_val_4039_);
lean_dec(v_val_4039_);
v_res_4041_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4040_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4044_){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_box(2);
v___x_4046_ = l_Lean_Syntax_mkStrLit(v_val_4044_, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4049_){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = l_Nat_reprFast(v_n_4049_);
v___x_4051_ = lean_box(2);
v___x_4052_ = l_Lean_Syntax_mkNumLit(v___x_4050_, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4060_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4061_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4062_ = lean_substring_tostring(v_s_4060_);
v___x_4063_ = lean_box(2);
v___x_4064_ = l_Lean_Syntax_mkStrLit(v___x_4062_, v___x_4063_);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_mk_empty_array_with_capacity(v___x_4065_);
v___x_4067_ = lean_array_push(v___x_4066_, v___x_4064_);
v___x_4068_ = l_Lean_Syntax_mkCApp(v___x_4061_, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4071_, lean_object* v_x_4072_){
_start:
{
switch(lean_obj_tag(v_x_4072_))
{
case 0:
{
uint8_t v___x_4073_; 
v___x_4073_ = l_List_isEmpty___redArg(v_acc_4071_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4074_, 0, v_acc_4071_);
return v___x_4074_;
}
else
{
lean_object* v___x_4075_; 
lean_dec(v_acc_4071_);
v___x_4075_ = lean_box(0);
return v___x_4075_;
}
}
case 1:
{
lean_object* v_pre_4076_; lean_object* v_str_4077_; lean_object* v_val_4079_; lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
v_pre_4076_ = lean_ctor_get(v_x_4072_, 0);
lean_inc(v_pre_4076_);
v_str_4077_ = lean_ctor_get(v_x_4072_, 1);
lean_inc_ref(v_str_4077_);
lean_dec_ref_known(v_x_4072_, 2);
v___x_4082_ = lean_unsigned_to_nat(0u);
v___x_4083_ = lean_string_utf8_byte_size(v_str_4077_);
v___x_4084_ = lean_nat_dec_lt(v___x_4082_, v___x_4083_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4085_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4086_ = lean_string_append(v___x_4085_, v_str_4077_);
lean_dec_ref(v_str_4077_);
v___x_4087_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4088_ = lean_string_append(v___x_4086_, v___x_4087_);
v_val_4079_ = v___x_4088_;
goto v___jp_4078_;
}
else
{
lean_object* v___f_4089_; uint8_t v___y_4091_; lean_object* v___f_4098_; uint32_t v___y_4105_; uint32_t v___y_4110_; uint8_t v___y_4111_; uint8_t v_c_4125_; uint8_t v___x_4134_; uint8_t v___x_4135_; 
v___f_4089_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4098_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4125_ = lean_string_get_byte_fast(v_str_4077_, v___x_4082_);
v___x_4134_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4135_ = lean_uint8_dec_le(v___x_4134_, v_c_4125_);
if (v___x_4135_ == 0)
{
goto v___jp_4129_;
}
else
{
uint8_t v___x_4136_; uint8_t v___x_4137_; 
v___x_4136_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4137_ = lean_uint8_dec_le(v_c_4125_, v___x_4136_);
if (v___x_4137_ == 0)
{
goto v___jp_4129_;
}
else
{
goto v___jp_4122_;
}
}
v___jp_4090_:
{
if (v___y_4091_ == 0)
{
uint8_t v___x_4092_; 
lean_inc_ref(v_str_4077_);
v___x_4092_ = lean_string_any(v_str_4077_, v___f_4089_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4093_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4094_ = lean_string_append(v___x_4093_, v_str_4077_);
lean_dec_ref(v_str_4077_);
v___x_4095_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4096_ = lean_string_append(v___x_4094_, v___x_4095_);
v_val_4079_ = v___x_4096_;
goto v___jp_4078_;
}
else
{
lean_object* v___x_4097_; 
lean_dec_ref(v_str_4077_);
lean_dec(v_pre_4076_);
lean_dec(v_acc_4071_);
v___x_4097_ = lean_box(0);
return v___x_4097_;
}
}
else
{
v_val_4079_ = v_str_4077_;
goto v___jp_4078_;
}
}
v___jp_4099_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
lean_inc_ref(v_str_4077_);
v___x_4100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4100_, 0, v_str_4077_);
lean_ctor_set(v___x_4100_, 1, v___x_4082_);
lean_ctor_set(v___x_4100_, 2, v___x_4083_);
v___x_4101_ = lean_unsigned_to_nat(1u);
v___x_4102_ = lean_substring_drop(v___x_4100_, v___x_4101_);
v___x_4103_ = lean_substring_all(v___x_4102_, v___f_4098_);
v___y_4091_ = v___x_4103_;
goto v___jp_4090_;
}
v___jp_4104_:
{
uint32_t v___x_4106_; uint8_t v___x_4107_; 
v___x_4106_ = 95;
v___x_4107_ = lean_uint32_dec_eq(v___y_4105_, v___x_4106_);
if (v___x_4107_ == 0)
{
uint8_t v___x_4108_; 
v___x_4108_ = l_Lean_isLetterLike(v___y_4105_);
if (v___x_4108_ == 0)
{
v___y_4091_ = v___x_4108_;
goto v___jp_4090_;
}
else
{
goto v___jp_4099_;
}
}
else
{
goto v___jp_4099_;
}
}
v___jp_4109_:
{
if (v___y_4111_ == 0)
{
uint32_t v___x_4112_; uint8_t v___x_4113_; 
v___x_4112_ = 97;
v___x_4113_ = lean_uint32_dec_le(v___x_4112_, v___y_4110_);
if (v___x_4113_ == 0)
{
v___y_4105_ = v___y_4110_;
goto v___jp_4104_;
}
else
{
uint32_t v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = 122;
v___x_4115_ = lean_uint32_dec_le(v___y_4110_, v___x_4114_);
if (v___x_4115_ == 0)
{
v___y_4105_ = v___y_4110_;
goto v___jp_4104_;
}
else
{
goto v___jp_4099_;
}
}
}
else
{
goto v___jp_4099_;
}
}
v___jp_4116_:
{
uint32_t v___x_4117_; uint32_t v___x_4118_; uint8_t v___x_4119_; 
v___x_4117_ = lean_string_utf8_get(v_str_4077_, v___x_4082_);
v___x_4118_ = 65;
v___x_4119_ = lean_uint32_dec_le(v___x_4118_, v___x_4117_);
if (v___x_4119_ == 0)
{
v___y_4110_ = v___x_4117_;
v___y_4111_ = v___x_4119_;
goto v___jp_4109_;
}
else
{
uint32_t v___x_4120_; uint8_t v___x_4121_; 
v___x_4120_ = 90;
v___x_4121_ = lean_uint32_dec_le(v___x_4117_, v___x_4120_);
v___y_4110_ = v___x_4117_;
v___y_4111_ = v___x_4121_;
goto v___jp_4109_;
}
}
v___jp_4122_:
{
lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4123_ = lean_unsigned_to_nat(1u);
v___x_4124_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4077_, v___x_4123_);
if (v___x_4124_ == 0)
{
goto v___jp_4116_;
}
else
{
v___y_4091_ = v___x_4124_;
goto v___jp_4090_;
}
}
v___jp_4126_:
{
uint8_t v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4128_ = lean_uint8_dec_eq(v_c_4125_, v___x_4127_);
if (v___x_4128_ == 0)
{
goto v___jp_4116_;
}
else
{
goto v___jp_4122_;
}
}
v___jp_4129_:
{
uint8_t v___x_4130_; uint8_t v___x_4131_; 
v___x_4130_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4131_ = lean_uint8_dec_le(v___x_4130_, v_c_4125_);
if (v___x_4131_ == 0)
{
goto v___jp_4126_;
}
else
{
uint8_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4133_ = lean_uint8_dec_le(v_c_4125_, v___x_4132_);
if (v___x_4133_ == 0)
{
goto v___jp_4126_;
}
else
{
goto v___jp_4122_;
}
}
}
}
v___jp_4078_:
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4080_, 0, v_val_4079_);
lean_ctor_set(v___x_4080_, 1, v_acc_4071_);
v_acc_4071_ = v___x_4080_;
v_x_4072_ = v_pre_4076_;
goto _start;
}
}
default: 
{
lean_object* v___x_4138_; 
lean_dec_ref_known(v_x_4072_, 2);
lean_dec(v_acc_4071_);
v___x_4138_ = lean_box(0);
return v___x_4138_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4146_ = l_Lean_mkCIdent(v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4157_){
_start:
{
switch(lean_obj_tag(v_x_4157_))
{
case 0:
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4158_;
}
case 1:
{
lean_object* v_pre_4159_; lean_object* v_str_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_pre_4159_ = lean_ctor_get(v_x_4157_, 0);
lean_inc(v_pre_4159_);
v_str_4160_ = lean_ctor_get(v_x_4157_, 1);
lean_inc_ref(v_str_4160_);
lean_dec_ref_known(v_x_4157_, 2);
v___x_4161_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4162_ = l_Lean_quoteNameMk(v_pre_4159_);
v___x_4163_ = lean_box(2);
v___x_4164_ = l_Lean_Syntax_mkStrLit(v_str_4160_, v___x_4163_);
v___x_4165_ = lean_unsigned_to_nat(2u);
v___x_4166_ = lean_mk_empty_array_with_capacity(v___x_4165_);
v___x_4167_ = lean_array_push(v___x_4166_, v___x_4162_);
v___x_4168_ = lean_array_push(v___x_4167_, v___x_4164_);
v___x_4169_ = l_Lean_Syntax_mkCApp(v___x_4161_, v___x_4168_);
return v___x_4169_;
}
default: 
{
lean_object* v_pre_4170_; lean_object* v_i_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v_pre_4170_ = lean_ctor_get(v_x_4157_, 0);
lean_inc(v_pre_4170_);
v_i_4171_ = lean_ctor_get(v_x_4157_, 1);
lean_inc(v_i_4171_);
lean_dec_ref_known(v_x_4157_, 2);
v___x_4172_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4173_ = l_Lean_quoteNameMk(v_pre_4170_);
v___x_4174_ = l_Nat_reprFast(v_i_4171_);
v___x_4175_ = lean_box(2);
v___x_4176_ = l_Lean_Syntax_mkNumLit(v___x_4174_, v___x_4175_);
v___x_4177_ = lean_unsigned_to_nat(2u);
v___x_4178_ = lean_mk_empty_array_with_capacity(v___x_4177_);
v___x_4179_ = lean_array_push(v___x_4178_, v___x_4173_);
v___x_4180_ = lean_array_push(v___x_4179_, v___x_4176_);
v___x_4181_ = l_Lean_Syntax_mkCApp(v___x_4172_, v___x_4180_);
return v___x_4181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4188_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_box(0);
lean_inc(v_n_4188_);
v___x_4190_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4189_, v_n_4188_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_quoteNameMk(v_n_4188_);
return v___x_4191_;
}
else
{
lean_object* v_val_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
lean_dec(v_n_4188_);
v_val_4192_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_val_4192_);
lean_dec_ref_known(v___x_4190_, 1);
v___x_4193_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4194_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4195_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4196_ = lean_string_intercalate(v___x_4195_, v_val_4192_);
v___x_4197_ = lean_string_append(v___x_4194_, v___x_4196_);
lean_dec_ref(v___x_4196_);
v___x_4198_ = lean_box(2);
v___x_4199_ = l_Lean_Syntax_mkNameLit(v___x_4197_, v___x_4198_);
v___x_4200_ = lean_unsigned_to_nat(1u);
v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4200_);
v___x_4202_ = lean_array_push(v___x_4201_, v___x_4199_);
v___x_4203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4198_);
lean_ctor_set(v___x_4203_, 1, v___x_4193_);
lean_ctor_set(v___x_4203_, 2, v___x_4202_);
return v___x_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4204_){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = lean_box(0);
lean_inc(v_n_4204_);
v___x_4206_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4205_, v_n_4204_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_quoteNameMk(v_n_4204_);
return v___x_4207_;
}
else
{
lean_object* v_val_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
lean_dec(v_n_4204_);
v_val_4208_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_val_4208_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4209_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4210_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4211_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4212_ = lean_string_intercalate(v___x_4211_, v_val_4208_);
v___x_4213_ = lean_string_append(v___x_4210_, v___x_4212_);
lean_dec_ref(v___x_4212_);
v___x_4214_ = lean_box(2);
v___x_4215_ = l_Lean_Syntax_mkNameLit(v___x_4213_, v___x_4214_);
v___x_4216_ = lean_unsigned_to_nat(1u);
v___x_4217_ = lean_mk_empty_array_with_capacity(v___x_4216_);
v___x_4218_ = lean_array_push(v___x_4217_, v___x_4215_);
v___x_4219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4214_);
lean_ctor_set(v___x_4219_, 1, v___x_4209_);
lean_ctor_set(v___x_4219_, 2, v___x_4218_);
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_x_4229_){
_start:
{
lean_object* v_fst_4230_; lean_object* v_snd_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_fst_4230_ = lean_ctor_get(v_x_4229_, 0);
lean_inc(v_fst_4230_);
v_snd_4231_ = lean_ctor_get(v_x_4229_, 1);
lean_inc(v_snd_4231_);
lean_dec_ref(v_x_4229_);
v___x_4232_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4233_ = lean_apply_1(v_inst_4227_, v_fst_4230_);
v___x_4234_ = lean_apply_1(v_inst_4228_, v_snd_4231_);
v___x_4235_ = lean_unsigned_to_nat(2u);
v___x_4236_ = lean_mk_empty_array_with_capacity(v___x_4235_);
v___x_4237_ = lean_array_push(v___x_4236_, v___x_4233_);
v___x_4238_ = lean_array_push(v___x_4237_, v___x_4234_);
v___x_4239_ = l_Lean_Syntax_mkCApp(v___x_4232_, v___x_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4240_, lean_object* v_inst_4241_){
_start:
{
lean_object* v___f_4242_; 
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4242_, 0, v_inst_4240_);
lean_closure_set(v___f_4242_, 1, v_inst_4241_);
return v___f_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4243_, lean_object* v_00_u03b2_4244_, lean_object* v_inst_4245_, lean_object* v_inst_4246_){
_start:
{
lean_object* v___f_4247_; 
v___f_4247_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4247_, 0, v_inst_4245_);
lean_closure_set(v___f_4247_, 1, v_inst_4246_);
return v___f_4247_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4254_ = l_Lean_mkCIdent(v___x_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4259_, lean_object* v_x_4260_){
_start:
{
if (lean_obj_tag(v_x_4260_) == 0)
{
lean_object* v___x_4261_; 
lean_dec_ref(v_inst_4259_);
v___x_4261_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4261_;
}
else
{
lean_object* v_head_4262_; lean_object* v_tail_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v_head_4262_ = lean_ctor_get(v_x_4260_, 0);
lean_inc(v_head_4262_);
v_tail_4263_ = lean_ctor_get(v_x_4260_, 1);
lean_inc(v_tail_4263_);
lean_dec_ref_known(v_x_4260_, 2);
v___x_4264_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4259_);
v___x_4265_ = lean_apply_1(v_inst_4259_, v_head_4262_);
v___x_4266_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4259_, v_tail_4263_);
v___x_4267_ = lean_unsigned_to_nat(2u);
v___x_4268_ = lean_mk_empty_array_with_capacity(v___x_4267_);
v___x_4269_ = lean_array_push(v___x_4268_, v___x_4265_);
v___x_4270_ = lean_array_push(v___x_4269_, v___x_4266_);
v___x_4271_ = l_Lean_Syntax_mkCApp(v___x_4264_, v___x_4270_);
return v___x_4271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4272_, lean_object* v_inst_4273_, lean_object* v_x_4274_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4273_, v_x_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4276_, v_a_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4279_, lean_object* v_inst_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4280_, v_a_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4284_, 0, lean_box(0));
lean_closure_set(v___x_4284_, 1, v_inst_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4285_, lean_object* v_inst_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4287_, 0, lean_box(0));
lean_closure_set(v___x_4287_, 1, v_inst_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4290_, lean_object* v_xs_4291_, lean_object* v_i_4292_, lean_object* v_args_4293_){
_start:
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_array_get_size(v_xs_4291_);
v___x_4295_ = lean_nat_dec_lt(v_i_4292_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
lean_dec(v_i_4292_);
lean_dec_ref(v_inst_4290_);
v___x_4296_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4297_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4298_ = l_Nat_reprFast(v___x_4294_);
v___x_4299_ = lean_string_append(v___x_4297_, v___x_4298_);
lean_dec_ref(v___x_4298_);
v___x_4300_ = l_Lean_Name_mkStr2(v___x_4296_, v___x_4299_);
v___x_4301_ = l_Lean_Syntax_mkCApp(v___x_4300_, v_args_4293_);
return v___x_4301_;
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4302_ = lean_unsigned_to_nat(1u);
v___x_4303_ = lean_nat_add(v_i_4292_, v___x_4302_);
v___x_4304_ = lean_array_fget_borrowed(v_xs_4291_, v_i_4292_);
lean_dec(v_i_4292_);
lean_inc_ref(v_inst_4290_);
lean_inc(v___x_4304_);
v___x_4305_ = lean_apply_1(v_inst_4290_, v___x_4304_);
v___x_4306_ = lean_array_push(v_args_4293_, v___x_4305_);
v_i_4292_ = v___x_4303_;
v_args_4293_ = v___x_4306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4308_, lean_object* v_xs_4309_, lean_object* v_i_4310_, lean_object* v_args_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4308_, v_xs_4309_, v_i_4310_, v_args_4311_);
lean_dec_ref(v_xs_4309_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4313_, lean_object* v_inst_4314_, lean_object* v_xs_4315_, lean_object* v_i_4316_, lean_object* v_args_4317_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4314_, v_xs_4315_, v_i_4316_, v_args_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4319_, lean_object* v_inst_4320_, lean_object* v_xs_4321_, lean_object* v_i_4322_, lean_object* v_args_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4319_, v_inst_4320_, v_xs_4321_, v_i_4322_, v_args_4323_);
lean_dec_ref(v_xs_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4329_, lean_object* v_xs_4330_){
_start:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4331_ = lean_array_get_size(v_xs_4330_);
v___x_4332_ = lean_unsigned_to_nat(8u);
v___x_4333_ = lean_nat_dec_le(v___x_4331_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4334_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4335_ = lean_array_to_list(v_xs_4330_);
v___x_4336_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4329_, v___x_4335_);
v___x_4337_ = lean_unsigned_to_nat(1u);
v___x_4338_ = lean_mk_empty_array_with_capacity(v___x_4337_);
v___x_4339_ = lean_array_push(v___x_4338_, v___x_4336_);
v___x_4340_ = l_Lean_Syntax_mkCApp(v___x_4334_, v___x_4339_);
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4343_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4329_, v_xs_4330_, v___x_4341_, v___x_4342_);
lean_dec_ref(v_xs_4330_);
return v___x_4343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4344_, lean_object* v_inst_4345_, lean_object* v_xs_4346_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4345_, v_xs_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4348_, lean_object* v_xs_4349_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4348_, v_xs_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4351_, lean_object* v_inst_4352_, lean_object* v_xs_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4352_, v_xs_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4356_, 0, lean_box(0));
lean_closure_set(v___x_4356_, 1, v_inst_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4357_, lean_object* v_inst_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4359_, 0, lean_box(0));
lean_closure_set(v___x_4359_, 1, v_inst_4358_);
return v___x_4359_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4365_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4366_ = l_Lean_mkIdent(v___x_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4371_, lean_object* v_x_4372_){
_start:
{
if (lean_obj_tag(v_x_4372_) == 0)
{
lean_object* v___x_4373_; 
lean_dec_ref(v_inst_4371_);
v___x_4373_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4373_;
}
else
{
lean_object* v_val_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_val_4374_ = lean_ctor_get(v_x_4372_, 0);
lean_inc(v_val_4374_);
lean_dec_ref_known(v_x_4372_, 1);
v___x_4375_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4376_ = lean_apply_1(v_inst_4371_, v_val_4374_);
v___x_4377_ = lean_unsigned_to_nat(1u);
v___x_4378_ = lean_mk_empty_array_with_capacity(v___x_4377_);
v___x_4379_ = lean_array_push(v___x_4378_, v___x_4376_);
v___x_4380_ = l_Lean_Syntax_mkCApp(v___x_4375_, v___x_4379_);
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4381_){
_start:
{
lean_object* v___f_4382_; 
v___f_4382_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4382_, 0, v_inst_4381_);
return v___f_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4383_, lean_object* v_inst_4384_){
_start:
{
lean_object* v___f_4385_; 
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4385_, 0, v_inst_4384_);
return v___f_4385_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4386_, lean_object* v_k_4387_){
_start:
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4389_ = lean_name_eq(v_k_4387_, v___x_4388_);
if (v___x_4389_ == 0)
{
uint8_t v___x_4390_; 
v___x_4390_ = 1;
return v___x_4390_;
}
else
{
return v___x_4386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4391_, lean_object* v_k_4392_){
_start:
{
uint8_t v___x_442__boxed_4393_; uint8_t v_res_4394_; lean_object* v_r_4395_; 
v___x_442__boxed_4393_ = lean_unbox(v___x_4391_);
v_res_4394_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4393_, v_k_4392_);
lean_dec(v_k_4392_);
v_r_4395_ = lean_box(v_res_4394_);
return v_r_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_){
_start:
{
lean_object* v_methods_4400_; lean_object* v_quotContext_4401_; lean_object* v_currMacroScope_4402_; lean_object* v_currRecDepth_4403_; lean_object* v_maxRecDepth_4404_; lean_object* v_ref_4405_; uint8_t v___x_4406_; 
v_methods_4400_ = lean_ctor_get(v_a_4398_, 0);
v_quotContext_4401_ = lean_ctor_get(v_a_4398_, 1);
v_currMacroScope_4402_ = lean_ctor_get(v_a_4398_, 2);
v_currRecDepth_4403_ = lean_ctor_get(v_a_4398_, 3);
v_maxRecDepth_4404_ = lean_ctor_get(v_a_4398_, 4);
v_ref_4405_ = lean_ctor_get(v_a_4398_, 5);
v___x_4406_ = lean_nat_dec_eq(v_currRecDepth_4403_, v_maxRecDepth_4404_);
if (v___x_4406_ == 0)
{
lean_object* v___x_4407_; lean_object* v___f_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4407_ = lean_box(v___x_4406_);
v___f_4408_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4408_, 0, v___x_4407_);
v___x_4409_ = lean_unsigned_to_nat(1u);
v___x_4410_ = lean_nat_add(v_currRecDepth_4403_, v___x_4409_);
lean_inc(v_ref_4405_);
lean_inc(v_maxRecDepth_4404_);
lean_inc(v_currMacroScope_4402_);
lean_inc(v_quotContext_4401_);
lean_inc(v_methods_4400_);
v___x_4411_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4411_, 0, v_methods_4400_);
lean_ctor_set(v___x_4411_, 1, v_quotContext_4401_);
lean_ctor_set(v___x_4411_, 2, v_currMacroScope_4402_);
lean_ctor_set(v___x_4411_, 3, v___x_4410_);
lean_ctor_set(v___x_4411_, 4, v_maxRecDepth_4404_);
lean_ctor_set(v___x_4411_, 5, v_ref_4405_);
lean_inc_ref(v___x_4411_);
v___x_4412_ = l_Lean_expandMacros(v_stx_4397_, v___f_4408_, v___x_4411_, v_a_4399_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4426_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
v_a_4414_ = lean_ctor_get(v___x_4412_, 1);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4416_ = v___x_4412_;
v_isShared_4417_ = v_isSharedCheck_4426_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_inc(v_a_4413_);
lean_dec(v___x_4412_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4426_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4418_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4413_);
v___x_4419_ = l_Lean_Syntax_isOfKind(v_a_4413_, v___x_4418_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
lean_del_object(v___x_4416_);
v___x_4420_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4421_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4413_, v___x_4420_, v___x_4411_, v_a_4414_);
lean_dec_ref_known(v___x_4411_, 6);
lean_dec(v_a_4413_);
return v___x_4421_;
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
lean_dec_ref_known(v___x_4411_, 6);
v___x_4422_ = l_Lean_TSyntax_getNat(v_a_4413_);
lean_dec(v_a_4413_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4422_);
v___x_4424_ = v___x_4416_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_a_4414_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref_known(v___x_4411_, 6);
v_a_4427_ = lean_ctor_get(v___x_4412_, 0);
v_a_4428_ = lean_ctor_get(v___x_4412_, 1);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4412_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_inc(v_a_4427_);
lean_dec(v___x_4412_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4427_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4436_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4437_, 0, v_stx_4397_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
lean_ctor_set(v___x_4438_, 1, v_a_4399_);
return v___x_4438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_evalPrec(v_stx_4439_, v_a_4440_, v_a_4441_);
lean_dec_ref(v_a_4440_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v_methods_4447_; lean_object* v_quotContext_4448_; lean_object* v_currMacroScope_4449_; lean_object* v_currRecDepth_4450_; lean_object* v_maxRecDepth_4451_; lean_object* v_ref_4452_; uint8_t v___x_4453_; 
v_methods_4447_ = lean_ctor_get(v_a_4445_, 0);
v_quotContext_4448_ = lean_ctor_get(v_a_4445_, 1);
v_currMacroScope_4449_ = lean_ctor_get(v_a_4445_, 2);
v_currRecDepth_4450_ = lean_ctor_get(v_a_4445_, 3);
v_maxRecDepth_4451_ = lean_ctor_get(v_a_4445_, 4);
v_ref_4452_ = lean_ctor_get(v_a_4445_, 5);
v___x_4453_ = lean_nat_dec_eq(v_currRecDepth_4450_, v_maxRecDepth_4451_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; lean_object* v___f_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4454_ = lean_box(v___x_4453_);
v___f_4455_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4455_, 0, v___x_4454_);
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = lean_nat_add(v_currRecDepth_4450_, v___x_4456_);
lean_inc(v_ref_4452_);
lean_inc(v_maxRecDepth_4451_);
lean_inc(v_currMacroScope_4449_);
lean_inc(v_quotContext_4448_);
lean_inc(v_methods_4447_);
v___x_4458_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4458_, 0, v_methods_4447_);
lean_ctor_set(v___x_4458_, 1, v_quotContext_4448_);
lean_ctor_set(v___x_4458_, 2, v_currMacroScope_4449_);
lean_ctor_set(v___x_4458_, 3, v___x_4457_);
lean_ctor_set(v___x_4458_, 4, v_maxRecDepth_4451_);
lean_ctor_set(v___x_4458_, 5, v_ref_4452_);
lean_inc_ref(v___x_4458_);
v___x_4459_ = l_Lean_expandMacros(v_stx_4444_, v___f_4455_, v___x_4458_, v_a_4446_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4473_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_a_4461_ = lean_ctor_get(v___x_4459_, 1);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4463_ = v___x_4459_;
v_isShared_4464_ = v_isSharedCheck_4473_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4473_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4465_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4460_);
v___x_4466_ = l_Lean_Syntax_isOfKind(v_a_4460_, v___x_4465_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_del_object(v___x_4463_);
v___x_4467_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4468_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4460_, v___x_4467_, v___x_4458_, v_a_4461_);
lean_dec_ref_known(v___x_4458_, 6);
lean_dec(v_a_4460_);
return v___x_4468_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
lean_dec_ref_known(v___x_4458_, 6);
v___x_4469_ = l_Lean_TSyntax_getNat(v_a_4460_);
lean_dec(v_a_4460_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4469_);
v___x_4471_ = v___x_4463_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_a_4461_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec_ref_known(v___x_4458_, 6);
v_a_4474_ = lean_ctor_get(v___x_4459_, 0);
v_a_4475_ = lean_ctor_get(v___x_4459_, 1);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4459_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_inc(v_a_4474_);
lean_dec(v___x_4459_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4474_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4484_, 0, v_stx_4444_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
v___x_4485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v_a_4446_);
return v___x_4485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_evalPrio(v_stx_4486_, v_a_4487_, v_a_4488_);
lean_dec_ref(v_a_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
if (lean_obj_tag(v_x_4490_) == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_unsigned_to_nat(1000u);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
lean_ctor_set(v___x_4494_, 1, v_a_4492_);
return v___x_4494_;
}
else
{
lean_object* v_val_4495_; lean_object* v___x_4496_; 
v_val_4495_ = lean_ctor_get(v_x_4490_, 0);
lean_inc(v_val_4495_);
lean_dec_ref_known(v_x_4490_, 1);
v___x_4496_ = l_Lean_evalPrio(v_val_4495_, v_a_4491_, v_a_4492_);
return v___x_4496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_evalOptPrio(v_x_4497_, v_a_4498_, v_a_4499_);
lean_dec_ref(v_a_4498_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4501_, lean_object* v_x1_4502_, lean_object* v_x2_4503_){
_start:
{
lean_object* v_fst_4504_; uint8_t v___x_4505_; 
v_fst_4504_ = lean_ctor_get(v_x1_4502_, 0);
v___x_4505_ = lean_unbox(v_fst_4504_);
if (v___x_4505_ == 0)
{
lean_object* v_snd_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v_x2_4503_);
v_snd_4506_ = lean_ctor_get(v_x1_4502_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_x1_4502_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; 
v_unused_4515_ = lean_ctor_get(v_x1_4502_, 0);
lean_dec(v_unused_4515_);
v___x_4508_ = v_x1_4502_;
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_snd_4506_);
lean_dec(v_x1_4502_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4512_; 
v___x_4510_ = lean_box(v___x_4501_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4510_);
v___x_4512_ = v___x_4508_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_snd_4506_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
else
{
lean_object* v_snd_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4526_; 
v_snd_4516_ = lean_ctor_get(v_x1_4502_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_x1_4502_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; 
v_unused_4527_ = lean_ctor_get(v_x1_4502_, 0);
lean_dec(v_unused_4527_);
v___x_4518_ = v_x1_4502_;
v_isShared_4519_ = v_isSharedCheck_4526_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_snd_4516_);
lean_dec(v_x1_4502_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4526_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
uint8_t v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4524_; 
v___x_4520_ = 0;
v___x_4521_ = lean_array_push(v_snd_4516_, v_x2_4503_);
v___x_4522_ = lean_box(v___x_4520_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 1, v___x_4521_);
lean_ctor_set(v___x_4518_, 0, v___x_4522_);
v___x_4524_ = v___x_4518_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4521_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4528_, lean_object* v_x1_4529_, lean_object* v_x2_4530_){
_start:
{
uint8_t v___x_87__boxed_4531_; lean_object* v_res_4532_; 
v___x_87__boxed_4531_ = lean_unbox(v___x_4528_);
v_res_4532_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4531_, v_x1_4529_, v_x2_4530_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4554_){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4555_ = lean_unsigned_to_nat(0u);
v___x_4556_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4557_ = lean_array_get_size(v_as_4554_);
v___x_4558_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4559_ = lean_nat_dec_lt(v___x_4555_, v___x_4557_);
if (v___x_4559_ == 0)
{
lean_dec_ref(v_as_4554_);
return v___x_4556_;
}
else
{
lean_object* v___x_4560_; lean_object* v___f_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; size_t v___x_4564_; size_t v___x_4565_; lean_object* v___x_4566_; lean_object* v_snd_4567_; 
v___x_4560_ = lean_box(v___x_4559_);
v___f_4561_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4561_, 0, v___x_4560_);
v___x_4562_ = lean_box(v___x_4559_);
v___x_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
lean_ctor_set(v___x_4563_, 1, v___x_4556_);
v___x_4564_ = ((size_t)0ULL);
v___x_4565_ = lean_usize_of_nat(v___x_4557_);
v___x_4566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4558_, v___f_4561_, v_as_4554_, v___x_4564_, v___x_4565_, v___x_4563_);
v_snd_4567_ = lean_ctor_get(v___x_4566_, 1);
lean_inc(v_snd_4567_);
lean_dec(v___x_4566_);
return v_snd_4567_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4568_, lean_object* v_as_4569_){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; 
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4572_ = lean_array_get_size(v_as_4569_);
v___x_4573_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4574_ = lean_nat_dec_lt(v___x_4570_, v___x_4572_);
if (v___x_4574_ == 0)
{
lean_dec_ref(v_as_4569_);
return v___x_4571_;
}
else
{
lean_object* v___x_4575_; lean_object* v___f_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; size_t v___x_4579_; size_t v___x_4580_; lean_object* v___x_4581_; lean_object* v_snd_4582_; 
v___x_4575_ = lean_box(v___x_4574_);
v___f_4576_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4576_, 0, v___x_4575_);
v___x_4577_ = lean_box(v___x_4574_);
v___x_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v___x_4571_);
v___x_4579_ = ((size_t)0ULL);
v___x_4580_ = lean_usize_of_nat(v___x_4572_);
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4573_, v___f_4576_, v_as_4569_, v___x_4579_, v___x_4580_, v___x_4578_);
v_snd_4582_ = lean_ctor_get(v___x_4581_, 1);
lean_inc(v_snd_4582_);
lean_dec(v___x_4581_);
return v_snd_4582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4583_, lean_object* v_inst_4584_, lean_object* v_a_4585_, lean_object* v_p_4586_, lean_object* v_acc_4587_, lean_object* v_stx_4588_, uint8_t v_____do__lift_4589_){
_start:
{
if (v_____do__lift_4589_ == 0)
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
lean_dec(v_stx_4588_);
v___x_4598_ = lean_unsigned_to_nat(2u);
v___x_4599_ = lean_nat_add(v_i_4583_, v___x_4598_);
v___x_4600_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4584_, v_a_4585_, v_p_4586_, v___x_4599_, v_acc_4587_);
return v___x_4600_;
}
else
{
lean_object* v___x_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4601_ = lean_array_get_size(v_acc_4587_);
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = lean_nat_dec_eq(v___x_4601_, v___x_4602_);
if (v___x_4603_ == 0)
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_nat_dec_eq(v_i_4583_, v___x_4602_);
if (v___x_4604_ == 0)
{
goto v___jp_4590_;
}
else
{
if (v___x_4603_ == 0)
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4605_ = lean_unsigned_to_nat(2u);
v___x_4606_ = lean_nat_add(v_i_4583_, v___x_4605_);
v___x_4607_ = lean_array_push(v_acc_4587_, v_stx_4588_);
v___x_4608_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4584_, v_a_4585_, v_p_4586_, v___x_4606_, v___x_4607_);
return v___x_4608_;
}
else
{
goto v___jp_4590_;
}
}
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4609_ = lean_unsigned_to_nat(2u);
v___x_4610_ = lean_nat_add(v_i_4583_, v___x_4609_);
v___x_4611_ = lean_array_push(v_acc_4587_, v_stx_4588_);
v___x_4612_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4584_, v_a_4585_, v_p_4586_, v___x_4610_, v___x_4611_);
return v___x_4612_;
}
}
v___jp_4590_:
{
lean_object* v___x_4591_; lean_object* v_sepStx_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4591_ = lean_nat_pred(v_i_4583_);
v_sepStx_4592_ = lean_array_fget_borrowed(v_a_4585_, v___x_4591_);
lean_dec(v___x_4591_);
v___x_4593_ = lean_unsigned_to_nat(2u);
v___x_4594_ = lean_nat_add(v_i_4583_, v___x_4593_);
lean_inc(v_sepStx_4592_);
v___x_4595_ = lean_array_push(v_acc_4587_, v_sepStx_4592_);
v___x_4596_ = lean_array_push(v___x_4595_, v_stx_4588_);
v___x_4597_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4584_, v_a_4585_, v_p_4586_, v___x_4594_, v___x_4596_);
return v___x_4597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4613_, lean_object* v_inst_4614_, lean_object* v_a_4615_, lean_object* v_p_4616_, lean_object* v_acc_4617_, lean_object* v_stx_4618_, lean_object* v_____do__lift_4619_){
_start:
{
uint8_t v_____do__lift_208__boxed_4620_; lean_object* v_res_4621_; 
v_____do__lift_208__boxed_4620_ = lean_unbox(v_____do__lift_4619_);
v_res_4621_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4613_, v_inst_4614_, v_a_4615_, v_p_4616_, v_acc_4617_, v_stx_4618_, v_____do__lift_208__boxed_4620_);
lean_dec(v_i_4613_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4622_, lean_object* v_a_4623_, lean_object* v_p_4624_, lean_object* v_i_4625_, lean_object* v_acc_4626_){
_start:
{
lean_object* v_toApplicative_4627_; lean_object* v_toBind_4628_; lean_object* v_toPure_4629_; lean_object* v___x_4630_; uint8_t v___x_4631_; 
v_toApplicative_4627_ = lean_ctor_get(v_inst_4622_, 0);
v_toBind_4628_ = lean_ctor_get(v_inst_4622_, 1);
lean_inc(v_toBind_4628_);
v_toPure_4629_ = lean_ctor_get(v_toApplicative_4627_, 1);
v___x_4630_ = lean_array_get_size(v_a_4623_);
v___x_4631_ = lean_nat_dec_lt(v_i_4625_, v___x_4630_);
if (v___x_4631_ == 0)
{
lean_object* v___x_4632_; 
lean_inc(v_toPure_4629_);
lean_dec(v_toBind_4628_);
lean_dec(v_i_4625_);
lean_dec(v_p_4624_);
lean_dec_ref(v_a_4623_);
lean_dec_ref(v_inst_4622_);
v___x_4632_ = lean_apply_2(v_toPure_4629_, lean_box(0), v_acc_4626_);
return v___x_4632_;
}
else
{
lean_object* v_stx_4633_; lean_object* v___f_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v_stx_4633_ = lean_array_fget(v_a_4623_, v_i_4625_);
lean_inc(v_stx_4633_);
lean_inc(v_p_4624_);
v___f_4634_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4634_, 0, v_i_4625_);
lean_closure_set(v___f_4634_, 1, v_inst_4622_);
lean_closure_set(v___f_4634_, 2, v_a_4623_);
lean_closure_set(v___f_4634_, 3, v_p_4624_);
lean_closure_set(v___f_4634_, 4, v_acc_4626_);
lean_closure_set(v___f_4634_, 5, v_stx_4633_);
v___x_4635_ = lean_apply_1(v_p_4624_, v_stx_4633_);
v___x_4636_ = lean_apply_4(v_toBind_4628_, lean_box(0), lean_box(0), v___x_4635_, v___f_4634_);
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4637_, lean_object* v_inst_4638_, lean_object* v_a_4639_, lean_object* v_p_4640_, lean_object* v_i_4641_, lean_object* v_acc_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4638_, v_a_4639_, v_p_4640_, v_i_4641_, v_acc_4642_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4644_, lean_object* v_a_4645_, lean_object* v_p_4646_){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = lean_unsigned_to_nat(0u);
v___x_4648_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4649_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4644_, v_a_4645_, v_p_4646_, v___x_4647_, v___x_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4650_, lean_object* v_inst_4651_, lean_object* v_a_4652_, lean_object* v_p_4653_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l_Array_filterSepElemsM___redArg(v_inst_4651_, v_a_4652_, v_p_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4655_, lean_object* v_x_4656_){
_start:
{
lean_object* v___x_4657_; uint8_t v___x_4658_; 
v___x_4657_ = lean_apply_1(v_p_4655_, v_x_4656_);
v___x_4658_ = lean_unbox(v___x_4657_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4659_, lean_object* v_x_4660_){
_start:
{
uint8_t v_res_4661_; lean_object* v_r_4662_; 
v_res_4661_ = l_Array_filterSepElems___lam__0(v_p_4659_, v_x_4660_);
v_r_4662_ = lean_box(v_res_4661_);
return v_r_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4663_, lean_object* v_p_4664_, lean_object* v_i_4665_, lean_object* v_acc_4666_){
_start:
{
lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4667_ = lean_array_get_size(v_a_4663_);
v___x_4668_ = lean_nat_dec_lt(v_i_4665_, v___x_4667_);
if (v___x_4668_ == 0)
{
lean_dec(v_i_4665_);
lean_dec_ref(v_p_4664_);
return v_acc_4666_;
}
else
{
lean_object* v_stx_4669_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v_stx_4669_ = lean_array_fget_borrowed(v_a_4663_, v_i_4665_);
lean_inc_ref(v_p_4664_);
lean_inc(v_stx_4669_);
v___x_4678_ = lean_apply_1(v_p_4664_, v_stx_4669_);
v___x_4679_ = lean_unbox(v___x_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = lean_unsigned_to_nat(2u);
v___x_4681_ = lean_nat_add(v_i_4665_, v___x_4680_);
lean_dec(v_i_4665_);
v_i_4665_ = v___x_4681_;
goto _start;
}
else
{
lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4683_ = lean_array_get_size(v_acc_4666_);
v___x_4684_ = lean_unsigned_to_nat(0u);
v___x_4685_ = lean_nat_dec_eq(v___x_4683_, v___x_4684_);
if (v___x_4685_ == 0)
{
uint8_t v___x_4686_; 
v___x_4686_ = lean_nat_dec_eq(v_i_4665_, v___x_4684_);
if (v___x_4686_ == 0)
{
goto v___jp_4670_;
}
else
{
if (v___x_4685_ == 0)
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4687_ = lean_unsigned_to_nat(2u);
v___x_4688_ = lean_nat_add(v_i_4665_, v___x_4687_);
lean_dec(v_i_4665_);
lean_inc(v_stx_4669_);
v___x_4689_ = lean_array_push(v_acc_4666_, v_stx_4669_);
v_i_4665_ = v___x_4688_;
v_acc_4666_ = v___x_4689_;
goto _start;
}
else
{
goto v___jp_4670_;
}
}
}
else
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = lean_unsigned_to_nat(2u);
v___x_4692_ = lean_nat_add(v_i_4665_, v___x_4691_);
lean_dec(v_i_4665_);
lean_inc(v_stx_4669_);
v___x_4693_ = lean_array_push(v_acc_4666_, v_stx_4669_);
v_i_4665_ = v___x_4692_;
v_acc_4666_ = v___x_4693_;
goto _start;
}
}
v___jp_4670_:
{
lean_object* v___x_4671_; lean_object* v_sepStx_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4671_ = lean_nat_pred(v_i_4665_);
v_sepStx_4672_ = lean_array_fget_borrowed(v_a_4663_, v___x_4671_);
lean_dec(v___x_4671_);
v___x_4673_ = lean_unsigned_to_nat(2u);
v___x_4674_ = lean_nat_add(v_i_4665_, v___x_4673_);
lean_dec(v_i_4665_);
lean_inc(v_sepStx_4672_);
v___x_4675_ = lean_array_push(v_acc_4666_, v_sepStx_4672_);
lean_inc(v_stx_4669_);
v___x_4676_ = lean_array_push(v___x_4675_, v_stx_4669_);
v_i_4665_ = v___x_4674_;
v_acc_4666_ = v___x_4676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4695_, lean_object* v_p_4696_, lean_object* v_i_4697_, lean_object* v_acc_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4695_, v_p_4696_, v_i_4697_, v_acc_4698_);
lean_dec_ref(v_a_4695_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4700_, lean_object* v_p_4701_){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___x_4703_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4704_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4700_, v_p_4701_, v___x_4702_, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4705_, lean_object* v_p_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4705_, v_p_4706_);
lean_dec_ref(v_a_4705_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4708_, lean_object* v_p_4709_){
_start:
{
lean_object* v___f_4710_; lean_object* v___x_4711_; 
v___f_4710_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4710_, 0, v_p_4709_);
v___x_4711_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4708_, v___f_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4712_, lean_object* v_p_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Array_filterSepElems(v_a_4712_, v_p_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4715_, lean_object* v_acc_4716_, lean_object* v_inst_4717_, lean_object* v_a_4718_, lean_object* v_f_4719_, lean_object* v_stx_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4715_, v_acc_4716_, v_inst_4717_, v_a_4718_, v_f_4719_, v_stx_4720_);
lean_dec(v_i_4715_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4722_, lean_object* v_a_4723_, lean_object* v_f_4724_, lean_object* v_i_4725_, lean_object* v_acc_4726_){
_start:
{
lean_object* v_toApplicative_4727_; lean_object* v_toBind_4728_; lean_object* v_toPure_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v_toApplicative_4727_ = lean_ctor_get(v_inst_4722_, 0);
v_toBind_4728_ = lean_ctor_get(v_inst_4722_, 1);
v_toPure_4729_ = lean_ctor_get(v_toApplicative_4727_, 1);
v___x_4730_ = lean_array_get_size(v_a_4723_);
v___x_4731_ = lean_nat_dec_lt(v_i_4725_, v___x_4730_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; 
lean_inc(v_toPure_4729_);
lean_dec(v_i_4725_);
lean_dec(v_f_4724_);
lean_dec_ref(v_a_4723_);
lean_dec_ref(v_inst_4722_);
v___x_4732_ = lean_apply_2(v_toPure_4729_, lean_box(0), v_acc_4726_);
return v___x_4732_;
}
else
{
lean_object* v_stx_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v_stx_4733_ = lean_array_fget_borrowed(v_a_4723_, v_i_4725_);
v___x_4734_ = lean_unsigned_to_nat(2u);
v___x_4735_ = lean_nat_mod(v_i_4725_, v___x_4734_);
v___x_4736_ = lean_unsigned_to_nat(0u);
v___x_4737_ = lean_nat_dec_eq(v___x_4735_, v___x_4736_);
lean_dec(v___x_4735_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4738_ = lean_unsigned_to_nat(1u);
v___x_4739_ = lean_nat_add(v_i_4725_, v___x_4738_);
lean_dec(v_i_4725_);
lean_inc(v_stx_4733_);
v___x_4740_ = lean_array_push(v_acc_4726_, v_stx_4733_);
v_i_4725_ = v___x_4739_;
v_acc_4726_ = v___x_4740_;
goto _start;
}
else
{
lean_object* v___f_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
lean_inc(v_stx_4733_);
lean_inc(v_toBind_4728_);
lean_inc(v_f_4724_);
v___f_4742_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4742_, 0, v_i_4725_);
lean_closure_set(v___f_4742_, 1, v_acc_4726_);
lean_closure_set(v___f_4742_, 2, v_inst_4722_);
lean_closure_set(v___f_4742_, 3, v_a_4723_);
lean_closure_set(v___f_4742_, 4, v_f_4724_);
v___x_4743_ = lean_apply_1(v_f_4724_, v_stx_4733_);
v___x_4744_ = lean_apply_4(v_toBind_4728_, lean_box(0), lean_box(0), v___x_4743_, v___f_4742_);
return v___x_4744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4745_, lean_object* v_acc_4746_, lean_object* v_inst_4747_, lean_object* v_a_4748_, lean_object* v_f_4749_, lean_object* v_stx_4750_){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4751_ = lean_unsigned_to_nat(1u);
v___x_4752_ = lean_nat_add(v_i_4745_, v___x_4751_);
v___x_4753_ = lean_array_push(v_acc_4746_, v_stx_4750_);
v___x_4754_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4747_, v_a_4748_, v_f_4749_, v___x_4752_, v___x_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4755_, lean_object* v_inst_4756_, lean_object* v_a_4757_, lean_object* v_f_4758_, lean_object* v_i_4759_, lean_object* v_acc_4760_){
_start:
{
lean_object* v___x_4761_; 
v___x_4761_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4756_, v_a_4757_, v_f_4758_, v_i_4759_, v_acc_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4762_, lean_object* v_a_4763_, lean_object* v_f_4764_){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4765_ = lean_unsigned_to_nat(0u);
v___x_4766_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4767_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4762_, v_a_4763_, v_f_4764_, v___x_4765_, v___x_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4768_, lean_object* v_inst_4769_, lean_object* v_a_4770_, lean_object* v_f_4771_){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_Array_mapSepElemsM___redArg(v_inst_4769_, v_a_4770_, v_f_4771_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4773_, lean_object* v_x_4774_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = lean_apply_1(v_f_4773_, v_x_4774_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4776_, lean_object* v_f_4777_, lean_object* v_i_4778_, lean_object* v_acc_4779_){
_start:
{
lean_object* v___x_4780_; uint8_t v___x_4781_; 
v___x_4780_ = lean_array_get_size(v_a_4776_);
v___x_4781_ = lean_nat_dec_lt(v_i_4778_, v___x_4780_);
if (v___x_4781_ == 0)
{
lean_dec(v_i_4778_);
lean_dec_ref(v_f_4777_);
return v_acc_4779_;
}
else
{
lean_object* v_stx_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v_stx_4782_ = lean_array_fget_borrowed(v_a_4776_, v_i_4778_);
v___x_4783_ = lean_unsigned_to_nat(2u);
v___x_4784_ = lean_nat_mod(v_i_4778_, v___x_4783_);
v___x_4785_ = lean_unsigned_to_nat(0u);
v___x_4786_ = lean_nat_dec_eq(v___x_4784_, v___x_4785_);
lean_dec(v___x_4784_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4787_ = lean_unsigned_to_nat(1u);
v___x_4788_ = lean_nat_add(v_i_4778_, v___x_4787_);
lean_dec(v_i_4778_);
lean_inc(v_stx_4782_);
v___x_4789_ = lean_array_push(v_acc_4779_, v_stx_4782_);
v_i_4778_ = v___x_4788_;
v_acc_4779_ = v___x_4789_;
goto _start;
}
else
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_inc_ref(v_f_4777_);
lean_inc(v_stx_4782_);
v___x_4791_ = lean_apply_1(v_f_4777_, v_stx_4782_);
v___x_4792_ = lean_unsigned_to_nat(1u);
v___x_4793_ = lean_nat_add(v_i_4778_, v___x_4792_);
lean_dec(v_i_4778_);
v___x_4794_ = lean_array_push(v_acc_4779_, v___x_4791_);
v_i_4778_ = v___x_4793_;
v_acc_4779_ = v___x_4794_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4796_, lean_object* v_f_4797_, lean_object* v_i_4798_, lean_object* v_acc_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4796_, v_f_4797_, v_i_4798_, v_acc_4799_);
lean_dec_ref(v_a_4796_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4801_, lean_object* v_f_4802_){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4805_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4801_, v_f_4802_, v___x_4803_, v___x_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4806_, lean_object* v_f_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4806_, v_f_4807_);
lean_dec_ref(v_a_4806_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4809_, lean_object* v_f_4810_){
_start:
{
lean_object* v___f_4811_; lean_object* v___x_4812_; 
v___f_4811_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4811_, 0, v_f_4810_);
v___x_4812_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4809_, v___f_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4813_, lean_object* v_f_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l_Array_mapSepElems(v_a_4813_, v_f_4814_);
lean_dec_ref(v_a_4813_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4816_, size_t v_i_4817_, size_t v_stop_4818_, lean_object* v_b_4819_){
_start:
{
lean_object* v___y_4821_; uint8_t v___x_4825_; 
v___x_4825_ = lean_usize_dec_eq(v_i_4817_, v_stop_4818_);
if (v___x_4825_ == 0)
{
lean_object* v_fst_4826_; uint8_t v___x_4827_; 
v_fst_4826_ = lean_ctor_get(v_b_4819_, 0);
v___x_4827_ = lean_unbox(v_fst_4826_);
if (v___x_4827_ == 0)
{
lean_object* v_snd_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4837_; 
v_snd_4828_ = lean_ctor_get(v_b_4819_, 1);
v_isSharedCheck_4837_ = !lean_is_exclusive(v_b_4819_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; 
v_unused_4838_ = lean_ctor_get(v_b_4819_, 0);
lean_dec(v_unused_4838_);
v___x_4830_ = v_b_4819_;
v_isShared_4831_ = v_isSharedCheck_4837_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_snd_4828_);
lean_dec(v_b_4819_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4837_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
uint8_t v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4832_ = 1;
v___x_4833_ = lean_box(v___x_4832_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v___x_4833_);
v___x_4835_ = v___x_4830_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4833_);
lean_ctor_set(v_reuseFailAlloc_4836_, 1, v_snd_4828_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
v___y_4821_ = v___x_4835_;
goto v___jp_4820_;
}
}
}
else
{
lean_object* v_snd_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4849_; 
v_snd_4839_ = lean_ctor_get(v_b_4819_, 1);
v_isSharedCheck_4849_ = !lean_is_exclusive(v_b_4819_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; 
v_unused_4850_ = lean_ctor_get(v_b_4819_, 0);
lean_dec(v_unused_4850_);
v___x_4841_ = v_b_4819_;
v_isShared_4842_ = v_isSharedCheck_4849_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_snd_4839_);
lean_dec(v_b_4819_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4849_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4843_ = lean_array_uget_borrowed(v_as_4816_, v_i_4817_);
lean_inc(v___x_4843_);
v___x_4844_ = lean_array_push(v_snd_4839_, v___x_4843_);
v___x_4845_ = lean_box(v___x_4825_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 1, v___x_4844_);
lean_ctor_set(v___x_4841_, 0, v___x_4845_);
v___x_4847_ = v___x_4841_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
lean_ctor_set(v_reuseFailAlloc_4848_, 1, v___x_4844_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
v___y_4821_ = v___x_4847_;
goto v___jp_4820_;
}
}
}
}
else
{
return v_b_4819_;
}
v___jp_4820_:
{
size_t v___x_4822_; size_t v___x_4823_; 
v___x_4822_ = ((size_t)1ULL);
v___x_4823_ = lean_usize_add(v_i_4817_, v___x_4822_);
v_i_4817_ = v___x_4823_;
v_b_4819_ = v___y_4821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4851_, lean_object* v_i_4852_, lean_object* v_stop_4853_, lean_object* v_b_4854_){
_start:
{
size_t v_i_boxed_4855_; size_t v_stop_boxed_4856_; lean_object* v_res_4857_; 
v_i_boxed_4855_ = lean_unbox_usize(v_i_4852_);
lean_dec(v_i_4852_);
v_stop_boxed_4856_ = lean_unbox_usize(v_stop_4853_);
lean_dec(v_stop_4853_);
v_res_4857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4851_, v_i_boxed_4855_, v_stop_boxed_4856_, v_b_4854_);
lean_dec_ref(v_as_4851_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4858_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4861_ = lean_array_get_size(v_sa_4858_);
v___x_4862_ = lean_nat_dec_lt(v___x_4859_, v___x_4861_);
if (v___x_4862_ == 0)
{
return v___x_4860_;
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; size_t v___x_4865_; size_t v___x_4866_; lean_object* v___x_4867_; lean_object* v_snd_4868_; 
v___x_4863_ = lean_box(v___x_4862_);
v___x_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
lean_ctor_set(v___x_4864_, 1, v___x_4860_);
v___x_4865_ = ((size_t)0ULL);
v___x_4866_ = lean_usize_of_nat(v___x_4861_);
v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4858_, v___x_4865_, v___x_4866_, v___x_4864_);
v_snd_4868_ = lean_ctor_get(v___x_4867_, 1);
lean_inc(v_snd_4868_);
lean_dec_ref(v___x_4867_);
return v_snd_4868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4869_);
lean_dec_ref(v_sa_4869_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4871_, lean_object* v_sa_4872_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4874_, lean_object* v_sa_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_Lean_Syntax_SepArray_getElems(v_sep_4874_, v_sa_4875_);
lean_dec_ref(v_sa_4875_);
lean_dec_ref(v_sep_4874_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4877_){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; uint8_t v___x_4881_; 
v___x_4878_ = lean_unsigned_to_nat(0u);
v___x_4879_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4880_ = lean_array_get_size(v_sa_4877_);
v___x_4881_ = lean_nat_dec_lt(v___x_4878_, v___x_4880_);
if (v___x_4881_ == 0)
{
return v___x_4879_;
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; size_t v___x_4884_; size_t v___x_4885_; lean_object* v___x_4886_; lean_object* v_snd_4887_; 
v___x_4882_ = lean_box(v___x_4881_);
v___x_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
lean_ctor_set(v___x_4883_, 1, v___x_4879_);
v___x_4884_ = ((size_t)0ULL);
v___x_4885_ = lean_usize_of_nat(v___x_4880_);
v___x_4886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4877_, v___x_4884_, v___x_4885_, v___x_4883_);
v_snd_4887_ = lean_ctor_get(v___x_4886_, 1);
lean_inc(v_snd_4887_);
lean_dec_ref(v___x_4886_);
return v_snd_4887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4888_);
lean_dec_ref(v_sa_4888_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4890_, lean_object* v_sep_4891_, lean_object* v_sa_4892_){
_start:
{
lean_object* v___x_4893_; 
v___x_4893_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4892_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4894_, lean_object* v_sep_4895_, lean_object* v_sa_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Lean_Syntax_TSepArray_getElems(v_k_4894_, v_sep_4895_, v_sa_4896_);
lean_dec_ref(v_sa_4896_);
lean_dec_ref(v_sep_4895_);
lean_dec(v_k_4894_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4898_, lean_object* v_sa_4899_, lean_object* v_e_4900_){
_start:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4901_ = lean_array_get_size(v_sa_4899_);
v___x_4902_ = lean_unsigned_to_nat(0u);
v___x_4903_ = lean_nat_dec_eq(v___x_4901_, v___x_4902_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4904_ = l_Lean_mkAtom(v_sep_4898_);
v___x_4905_ = lean_array_push(v_sa_4899_, v___x_4904_);
v___x_4906_ = lean_array_push(v___x_4905_, v_e_4900_);
return v___x_4906_;
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec_ref(v_sa_4899_);
lean_dec_ref(v_sep_4898_);
v___x_4907_ = lean_unsigned_to_nat(1u);
v___x_4908_ = lean_mk_empty_array_with_capacity(v___x_4907_);
v___x_4909_ = lean_array_push(v___x_4908_, v_e_4900_);
return v___x_4909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4910_, lean_object* v_sep_4911_, lean_object* v_sa_4912_, lean_object* v_e_4913_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4911_, v_sa_4912_, v_e_4913_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4915_, lean_object* v_sep_4916_, lean_object* v_sa_4917_, lean_object* v_e_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Syntax_TSepArray_push(v_k_4915_, v_sep_4916_, v_sa_4917_, v_e_4918_);
lean_dec(v_k_4915_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4923_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4925_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4927_);
lean_dec_ref(v_sep_4927_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4930_; 
v___x_4930_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4932_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4934_, lean_object* v_k_4935_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4937_, lean_object* v_k_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4937_, v_k_4938_);
lean_dec_ref(v_k_4938_);
lean_dec(v_sep_4937_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4940_){
_start:
{
lean_inc_ref(v_v_4940_);
return v_v_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4941_);
lean_dec_ref(v_v_4941_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4945_; 
v___f_4945_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4948_, lean_object* v_sep_4949_){
_start:
{
lean_object* v___f_4950_; 
v___f_4950_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4951_, lean_object* v_sep_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4951_, v_sep_4952_);
lean_dec_ref(v_sep_4952_);
lean_dec(v_k_4951_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4954_, lean_object* v_sep_4955_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4956_, 0, v_k_4954_);
lean_closure_set(v___x_4956_, 1, v_sep_4955_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4957_, lean_object* v_x_4958_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = lean_apply_1(v_inst_4957_, v_x_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v___x_4962_; size_t v_sz_4963_; size_t v___x_4964_; lean_object* v___x_4965_; 
v___x_4962_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4963_ = lean_array_size(v_a_4961_);
v___x_4964_ = ((size_t)0ULL);
v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4962_, v___f_4960_, v_sz_4963_, v___x_4964_, v_a_4961_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_4966_){
_start:
{
lean_object* v___f_4967_; lean_object* v___f_4968_; 
v___f_4967_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4967_, 0, v_inst_4966_);
v___f_4968_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4968_, 0, v___f_4967_);
return v___f_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_4969_, lean_object* v_k_x27_4970_, lean_object* v_inst_4971_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_4971_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_4973_, lean_object* v_k_x27_4974_, lean_object* v_inst_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_4973_, v_k_x27_4974_, v_inst_4975_);
lean_dec(v_k_x27_4974_);
lean_dec(v_k_4973_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_4977_){
_start:
{
lean_inc_ref(v_a_4977_);
return v_a_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_4978_);
lean_dec_ref(v_a_4978_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_4982_; 
v___f_4982_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_4985_){
_start:
{
lean_object* v___f_4986_; 
v___f_4986_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_4987_);
lean_dec(v_k_4987_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_4996_){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_4997_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_4998_ = lean_box(2);
v___x_4999_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5000_ = lean_unsigned_to_nat(2u);
v___x_5001_ = lean_mk_empty_array_with_capacity(v___x_5000_);
v___x_5002_ = lean_array_push(v___x_5001_, v_id_4996_);
v___x_5003_ = lean_array_push(v___x_5002_, v___x_4999_);
v___x_5004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5004_, 0, v___x_4998_);
lean_ctor_set(v___x_5004_, 1, v___x_4997_);
lean_ctor_set(v___x_5004_, 2, v___x_5003_);
return v___x_5004_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = 123;
v___x_5009_ = lean_box_uint32(v___x_5008_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5010_, lean_object* v_i_5011_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Lean_Syntax_decodeQuotedChar(v_s_5010_, v_i_5011_);
if (lean_obj_tag(v___x_5012_) == 0)
{
uint32_t v_c_5013_; uint32_t v___x_5014_; uint8_t v___x_5015_; 
v_c_5013_ = lean_string_utf8_get(v_s_5010_, v_i_5011_);
v___x_5014_ = 123;
v___x_5015_ = lean_uint32_dec_eq(v_c_5013_, v___x_5014_);
if (v___x_5015_ == 0)
{
return v___x_5012_;
}
else
{
lean_object* v_i_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v_i_5016_ = lean_string_utf8_next(v_s_5010_, v_i_5011_);
v___x_5017_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
lean_ctor_set(v___x_5018_, 1, v_i_5016_);
v___x_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
return v___x_5019_;
}
}
else
{
return v___x_5012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5020_, lean_object* v_i_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5020_, v_i_5021_);
lean_dec(v_i_5021_);
lean_dec_ref(v_s_5020_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5023_, lean_object* v_i_5024_, lean_object* v_acc_5025_){
_start:
{
uint32_t v_c_5026_; uint32_t v___x_5027_; uint8_t v___x_5028_; 
v_c_5026_ = lean_string_utf8_get(v_s_5023_, v_i_5024_);
v___x_5027_ = 34;
v___x_5028_ = lean_uint32_dec_eq(v_c_5026_, v___x_5027_);
if (v___x_5028_ == 0)
{
uint32_t v___x_5029_; uint8_t v___x_5030_; 
v___x_5029_ = 123;
v___x_5030_ = lean_uint32_dec_eq(v_c_5026_, v___x_5029_);
if (v___x_5030_ == 0)
{
lean_object* v_i_5031_; uint8_t v___x_5032_; 
v_i_5031_ = lean_string_utf8_next(v_s_5023_, v_i_5024_);
lean_dec(v_i_5024_);
v___x_5032_ = lean_string_utf8_at_end(v_s_5023_, v_i_5031_);
if (v___x_5032_ == 0)
{
uint32_t v___x_5033_; uint8_t v___x_5034_; 
v___x_5033_ = 92;
v___x_5034_ = lean_uint32_dec_eq(v_c_5026_, v___x_5033_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; 
v___x_5035_ = lean_string_push(v_acc_5025_, v_c_5026_);
v_i_5024_ = v_i_5031_;
v_acc_5025_ = v___x_5035_;
goto _start;
}
else
{
lean_object* v___x_5037_; 
v___x_5037_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5023_, v_i_5031_);
if (lean_obj_tag(v___x_5037_) == 1)
{
lean_object* v_val_5038_; lean_object* v_fst_5039_; lean_object* v_snd_5040_; uint32_t v___x_5041_; lean_object* v___x_5042_; 
lean_dec(v_i_5031_);
v_val_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_val_5038_);
lean_dec_ref_known(v___x_5037_, 1);
v_fst_5039_ = lean_ctor_get(v_val_5038_, 0);
lean_inc(v_fst_5039_);
v_snd_5040_ = lean_ctor_get(v_val_5038_, 1);
lean_inc(v_snd_5040_);
lean_dec(v_val_5038_);
v___x_5041_ = lean_unbox_uint32(v_fst_5039_);
lean_dec(v_fst_5039_);
v___x_5042_ = lean_string_push(v_acc_5025_, v___x_5041_);
v_i_5024_ = v_snd_5040_;
v_acc_5025_ = v___x_5042_;
goto _start;
}
else
{
lean_object* v___x_5044_; 
lean_dec(v___x_5037_);
lean_inc_ref(v_s_5023_);
v___x_5044_ = l_Lean_Syntax_decodeStringGap(v_s_5023_, v_i_5031_);
lean_dec(v_i_5031_);
if (lean_obj_tag(v___x_5044_) == 1)
{
lean_object* v_val_5045_; 
v_val_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_val_5045_);
lean_dec_ref_known(v___x_5044_, 1);
v_i_5024_ = v_val_5045_;
goto _start;
}
else
{
lean_object* v___x_5047_; 
lean_dec(v___x_5044_);
lean_dec_ref(v_acc_5025_);
lean_dec_ref(v_s_5023_);
v___x_5047_ = lean_box(0);
return v___x_5047_;
}
}
}
}
else
{
lean_object* v___x_5048_; 
lean_dec(v_i_5031_);
lean_dec_ref(v_acc_5025_);
lean_dec_ref(v_s_5023_);
v___x_5048_ = lean_box(0);
return v___x_5048_;
}
}
else
{
lean_object* v___x_5049_; 
lean_dec(v_i_5024_);
lean_dec_ref(v_s_5023_);
v___x_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5049_, 0, v_acc_5025_);
return v___x_5049_;
}
}
else
{
lean_object* v___x_5050_; 
lean_dec(v_i_5024_);
lean_dec_ref(v_s_5023_);
v___x_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5050_, 0, v_acc_5025_);
return v___x_5050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5051_){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = lean_unsigned_to_nat(1u);
v___x_5053_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5054_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5051_, v___x_5052_, v___x_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5058_){
_start:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5060_ = l_Lean_Syntax_isLit_x3f(v___x_5059_, v_stx_5058_);
if (lean_obj_tag(v___x_5060_) == 0)
{
return v___x_5060_;
}
else
{
lean_object* v_val_5061_; lean_object* v___x_5062_; 
v_val_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_val_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5061_);
return v___x_5062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5063_);
lean_dec(v_stx_5063_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5065_){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; 
v___x_5066_ = l_Lean_Syntax_getArgs(v_stx_5065_);
v___x_5067_ = lean_unsigned_to_nat(0u);
v___x_5068_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5069_ = lean_array_get_size(v___x_5066_);
v___x_5070_ = lean_nat_dec_lt(v___x_5067_, v___x_5069_);
if (v___x_5070_ == 0)
{
lean_dec_ref(v___x_5066_);
return v___x_5068_;
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5072_; size_t v___x_5073_; size_t v___x_5074_; lean_object* v___x_5075_; lean_object* v_snd_5076_; 
v___x_5071_ = lean_box(v___x_5070_);
v___x_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
lean_ctor_set(v___x_5072_, 1, v___x_5068_);
v___x_5073_ = ((size_t)0ULL);
v___x_5074_ = lean_usize_of_nat(v___x_5069_);
v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5066_, v___x_5073_, v___x_5074_, v___x_5072_);
lean_dec_ref(v___x_5066_);
v_snd_5076_ = lean_ctor_get(v___x_5075_, 1);
lean_inc(v_snd_5076_);
lean_dec_ref(v___x_5075_);
return v_snd_5076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Syntax_getSepArgs(v_stx_5077_);
lean_dec(v_stx_5077_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5079_, lean_object* v_mkElem_5080_, lean_object* v_mkLit_5081_, lean_object* v_as_5082_, size_t v_sz_5083_, size_t v_i_5084_, lean_object* v_b_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v_a_5089_; lean_object* v_a_5090_; lean_object* v_elem_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; uint8_t v___x_5102_; 
v___x_5102_ = lean_usize_dec_lt(v_i_5084_, v_sz_5083_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; 
lean_dec_ref(v_mkLit_5081_);
lean_dec_ref(v_mkElem_5080_);
lean_dec_ref(v_mkAppend_5079_);
v___x_5103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5103_, 0, v_b_5085_);
lean_ctor_set(v___x_5103_, 1, v___y_5087_);
return v___x_5103_;
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5105_; 
v_a_5104_ = lean_array_uget_borrowed(v_as_5082_, v_i_5084_);
v___x_5105_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5104_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_methods_5106_; lean_object* v_quotContext_5107_; lean_object* v_currMacroScope_5108_; lean_object* v_currRecDepth_5109_; lean_object* v_maxRecDepth_5110_; lean_object* v_ref_5111_; lean_object* v_ref_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
v_methods_5106_ = lean_ctor_get(v___y_5086_, 0);
v_quotContext_5107_ = lean_ctor_get(v___y_5086_, 1);
v_currMacroScope_5108_ = lean_ctor_get(v___y_5086_, 2);
v_currRecDepth_5109_ = lean_ctor_get(v___y_5086_, 3);
v_maxRecDepth_5110_ = lean_ctor_get(v___y_5086_, 4);
v_ref_5111_ = lean_ctor_get(v___y_5086_, 5);
v_ref_5112_ = l_Lean_replaceRef(v_a_5104_, v_ref_5111_);
lean_inc(v_maxRecDepth_5110_);
lean_inc(v_currRecDepth_5109_);
lean_inc(v_currMacroScope_5108_);
lean_inc(v_quotContext_5107_);
lean_inc(v_methods_5106_);
v___x_5113_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5113_, 0, v_methods_5106_);
lean_ctor_set(v___x_5113_, 1, v_quotContext_5107_);
lean_ctor_set(v___x_5113_, 2, v_currMacroScope_5108_);
lean_ctor_set(v___x_5113_, 3, v_currRecDepth_5109_);
lean_ctor_set(v___x_5113_, 4, v_maxRecDepth_5110_);
lean_ctor_set(v___x_5113_, 5, v_ref_5112_);
lean_inc_ref(v_mkElem_5080_);
lean_inc(v_a_5104_);
v___x_5114_ = lean_apply_3(v_mkElem_5080_, v_a_5104_, v___x_5113_, v___y_5087_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v_a_5115_; lean_object* v_a_5116_; 
v_a_5115_ = lean_ctor_get(v___x_5114_, 0);
lean_inc(v_a_5115_);
v_a_5116_ = lean_ctor_get(v___x_5114_, 1);
lean_inc(v_a_5116_);
lean_dec_ref_known(v___x_5114_, 2);
v_elem_5095_ = v_a_5115_;
v___y_5096_ = v___y_5086_;
v___y_5097_ = v_a_5116_;
goto v___jp_5094_;
}
else
{
lean_dec(v_b_5085_);
lean_dec_ref(v_mkLit_5081_);
lean_dec_ref(v_mkElem_5080_);
lean_dec_ref(v_mkAppend_5079_);
return v___x_5114_;
}
}
else
{
lean_object* v_val_5117_; uint8_t v___x_5118_; 
v_val_5117_ = lean_ctor_get(v___x_5105_, 0);
lean_inc_n(v_val_5117_, 2);
lean_dec_ref_known(v___x_5105_, 1);
v___x_5118_ = lean_string_isempty(v_val_5117_);
if (v___x_5118_ == 0)
{
lean_object* v_methods_5119_; lean_object* v_quotContext_5120_; lean_object* v_currMacroScope_5121_; lean_object* v_currRecDepth_5122_; lean_object* v_maxRecDepth_5123_; lean_object* v_ref_5124_; lean_object* v_ref_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v_methods_5119_ = lean_ctor_get(v___y_5086_, 0);
v_quotContext_5120_ = lean_ctor_get(v___y_5086_, 1);
v_currMacroScope_5121_ = lean_ctor_get(v___y_5086_, 2);
v_currRecDepth_5122_ = lean_ctor_get(v___y_5086_, 3);
v_maxRecDepth_5123_ = lean_ctor_get(v___y_5086_, 4);
v_ref_5124_ = lean_ctor_get(v___y_5086_, 5);
v_ref_5125_ = l_Lean_replaceRef(v_a_5104_, v_ref_5124_);
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
lean_inc_ref(v_mkLit_5081_);
v___x_5127_ = lean_apply_3(v_mkLit_5081_, v_val_5117_, v___x_5126_, v___y_5087_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v_a_5129_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
v_a_5129_ = lean_ctor_get(v___x_5127_, 1);
lean_inc(v_a_5129_);
lean_dec_ref_known(v___x_5127_, 2);
v_elem_5095_ = v_a_5128_;
v___y_5096_ = v___y_5086_;
v___y_5097_ = v_a_5129_;
goto v___jp_5094_;
}
else
{
lean_dec(v_b_5085_);
lean_dec_ref(v_mkLit_5081_);
lean_dec_ref(v_mkElem_5080_);
lean_dec_ref(v_mkAppend_5079_);
return v___x_5127_;
}
}
else
{
lean_dec(v_val_5117_);
v_a_5089_ = v_b_5085_;
v_a_5090_ = v___y_5087_;
goto v___jp_5088_;
}
}
}
v___jp_5088_:
{
size_t v___x_5091_; size_t v___x_5092_; 
v___x_5091_ = ((size_t)1ULL);
v___x_5092_ = lean_usize_add(v_i_5084_, v___x_5091_);
v_i_5084_ = v___x_5092_;
v_b_5085_ = v_a_5089_;
v___y_5087_ = v_a_5090_;
goto _start;
}
v___jp_5094_:
{
uint8_t v___x_5098_; 
v___x_5098_ = l_Lean_Syntax_isMissing(v_b_5085_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; 
lean_inc_ref(v_mkAppend_5079_);
lean_inc_ref(v___y_5096_);
v___x_5099_ = lean_apply_4(v_mkAppend_5079_, v_b_5085_, v_elem_5095_, v___y_5096_, v___y_5097_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; lean_object* v_a_5101_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_a_5100_);
v_a_5101_ = lean_ctor_get(v___x_5099_, 1);
lean_inc(v_a_5101_);
lean_dec_ref_known(v___x_5099_, 2);
v_a_5089_ = v_a_5100_;
v_a_5090_ = v_a_5101_;
goto v___jp_5088_;
}
else
{
lean_dec_ref(v_mkLit_5081_);
lean_dec_ref(v_mkElem_5080_);
lean_dec_ref(v_mkAppend_5079_);
return v___x_5099_;
}
}
else
{
lean_dec(v_b_5085_);
v_a_5089_ = v_elem_5095_;
v_a_5090_ = v___y_5097_;
goto v___jp_5088_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5130_, lean_object* v_mkElem_5131_, lean_object* v_mkLit_5132_, lean_object* v_as_5133_, lean_object* v_sz_5134_, lean_object* v_i_5135_, lean_object* v_b_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
size_t v_sz_boxed_5139_; size_t v_i_boxed_5140_; lean_object* v_res_5141_; 
v_sz_boxed_5139_ = lean_unbox_usize(v_sz_5134_);
lean_dec(v_sz_5134_);
v_i_boxed_5140_ = lean_unbox_usize(v_i_5135_);
lean_dec(v_i_5135_);
v_res_5141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5130_, v_mkElem_5131_, v_mkLit_5132_, v_as_5133_, v_sz_boxed_5139_, v_i_boxed_5140_, v_b_5136_, v___y_5137_, v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec_ref(v_as_5133_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5142_, lean_object* v_mkAppend_5143_, lean_object* v_mkElem_5144_, lean_object* v_mkLit_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_){
_start:
{
lean_object* v_result_5148_; size_t v_sz_5149_; size_t v___x_5150_; lean_object* v___x_5151_; 
v_result_5148_ = lean_box(0);
v_sz_5149_ = lean_array_size(v_chunks_5142_);
v___x_5150_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5145_);
v___x_5151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5143_, v_mkElem_5144_, v_mkLit_5145_, v_chunks_5142_, v_sz_5149_, v___x_5150_, v_result_5148_, v_a_5146_, v_a_5147_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; lean_object* v_a_5153_; uint8_t v___x_5154_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
v_a_5153_ = lean_ctor_get(v___x_5151_, 1);
lean_inc(v_a_5153_);
v___x_5154_ = l_Lean_Syntax_isMissing(v_a_5152_);
lean_dec(v_a_5152_);
if (v___x_5154_ == 0)
{
lean_dec(v_a_5153_);
lean_dec_ref(v_mkLit_5145_);
return v___x_5151_;
}
else
{
lean_object* v___x_5155_; lean_object* v___x_5156_; 
lean_dec_ref_known(v___x_5151_, 2);
v___x_5155_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5146_);
v___x_5156_ = lean_apply_3(v_mkLit_5145_, v___x_5155_, v_a_5146_, v_a_5153_);
return v___x_5156_;
}
}
else
{
lean_dec_ref(v_mkLit_5145_);
return v___x_5151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5157_, lean_object* v_mkAppend_5158_, lean_object* v_mkElem_5159_, lean_object* v_mkLit_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5157_, v_mkAppend_5158_, v_mkElem_5159_, v_mkLit_5160_, v_a_5161_, v_a_5162_);
lean_dec_ref(v_a_5161_);
lean_dec_ref(v_chunks_5157_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5168_, lean_object* v_b_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v_ref_5172_; uint8_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; 
v_ref_5172_ = lean_ctor_get(v___y_5170_, 5);
v___x_5173_ = 0;
v___x_5174_ = l_Lean_SourceInfo_fromRef(v_ref_5172_, v___x_5173_);
v___x_5175_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5176_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5174_);
v___x_5177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5174_);
lean_ctor_set(v___x_5177_, 1, v___x_5176_);
v___x_5178_ = l_Lean_Syntax_node3(v___x_5174_, v___x_5175_, v_a_5168_, v___x_5177_, v_b_5169_);
v___x_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5178_);
lean_ctor_set(v___x_5179_, 1, v___y_5171_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5180_, lean_object* v_b_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5180_, v_b_5181_, v___y_5182_, v___y_5183_);
lean_dec_ref(v___y_5182_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5185_, lean_object* v_a_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_ref_5189_; uint8_t v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v_ref_5189_ = lean_ctor_get(v___y_5187_, 5);
v___x_5190_ = 0;
v___x_5191_ = l_Lean_SourceInfo_fromRef(v_ref_5189_, v___x_5190_);
v___x_5192_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5193_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5191_);
v___x_5194_ = l_Lean_Syntax_node1(v___x_5191_, v___x_5193_, v_a_5186_);
v___x_5195_ = l_Lean_Syntax_node2(v___x_5191_, v___x_5192_, v_ofInterpFn_5185_, v___x_5194_);
v___x_5196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5195_);
lean_ctor_set(v___x_5196_, 1, v___y_5188_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5197_, lean_object* v_a_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5197_, v_a_5198_, v___y_5199_, v___y_5200_);
lean_dec_ref(v___y_5199_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5202_, lean_object* v_s_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v_ref_5206_; uint8_t v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v_ref_5206_ = lean_ctor_get(v___y_5204_, 5);
v___x_5207_ = 0;
v___x_5208_ = l_Lean_SourceInfo_fromRef(v_ref_5206_, v___x_5207_);
v___x_5209_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5210_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5211_ = lean_box(2);
v___x_5212_ = l_Lean_Syntax_mkStrLit(v_s_5203_, v___x_5211_);
lean_inc(v___x_5208_);
v___x_5213_ = l_Lean_Syntax_node1(v___x_5208_, v___x_5210_, v___x_5212_);
v___x_5214_ = l_Lean_Syntax_node2(v___x_5208_, v___x_5209_, v_ofLitFn_5202_, v___x_5213_);
v___x_5215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5214_);
lean_ctor_set(v___x_5215_, 1, v___y_5205_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5216_, lean_object* v_s_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5216_, v_s_5217_, v___y_5218_, v___y_5219_);
lean_dec_ref(v___y_5218_);
return v_res_5220_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5238_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5239_ = l_String_toRawSubstring_x27(v___x_5238_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5260_, lean_object* v_type_5261_, lean_object* v_ofInterpFn_5262_, lean_object* v_ofLitFn_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v___f_5266_; lean_object* v___f_5267_; lean_object* v___f_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___f_5266_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5267_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5267_, 0, v_ofInterpFn_5262_);
v___f_5268_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5268_, 0, v_ofLitFn_5263_);
v___x_5269_ = l_Lean_Syntax_getArgs(v_interpStr_5260_);
v___x_5270_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5269_, v___f_5266_, v___f_5267_, v___f_5268_, v_a_5264_, v_a_5265_);
lean_dec_ref(v___x_5269_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_object* v_a_5271_; lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5303_; 
v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
v_a_5272_ = lean_ctor_get(v___x_5270_, 1);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5274_ = v___x_5270_;
v_isShared_5275_ = v_isSharedCheck_5303_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_inc(v_a_5271_);
lean_dec(v___x_5270_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5303_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v_quotContext_5276_; lean_object* v_currMacroScope_5277_; lean_object* v_ref_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5301_; 
v_quotContext_5276_ = lean_ctor_get(v_a_5264_, 1);
v_currMacroScope_5277_ = lean_ctor_get(v_a_5264_, 2);
v_ref_5278_ = lean_ctor_get(v_a_5264_, 5);
v___x_5279_ = 0;
v___x_5280_ = l_Lean_SourceInfo_fromRef(v_ref_5278_, v___x_5279_);
v___x_5281_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5282_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5283_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5280_, 7);
v___x_5284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5280_);
lean_ctor_set(v___x_5284_, 1, v___x_5283_);
v___x_5285_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5286_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5287_ = lean_box(0);
lean_inc(v_currMacroScope_5277_);
lean_inc(v_quotContext_5276_);
v___x_5288_ = l_Lean_addMacroScope(v_quotContext_5276_, v___x_5287_, v_currMacroScope_5277_);
v___x_5289_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5290_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5280_);
lean_ctor_set(v___x_5290_, 1, v___x_5286_);
lean_ctor_set(v___x_5290_, 2, v___x_5288_);
lean_ctor_set(v___x_5290_, 3, v___x_5289_);
v___x_5291_ = l_Lean_Syntax_node1(v___x_5280_, v___x_5285_, v___x_5290_);
v___x_5292_ = l_Lean_Syntax_node2(v___x_5280_, v___x_5282_, v___x_5284_, v___x_5291_);
v___x_5293_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5280_);
lean_ctor_set(v___x_5294_, 1, v___x_5293_);
v___x_5295_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5296_ = l_Lean_Syntax_node1(v___x_5280_, v___x_5295_, v_type_5261_);
v___x_5297_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5280_);
lean_ctor_set(v___x_5298_, 1, v___x_5297_);
v___x_5299_ = l_Lean_Syntax_node5(v___x_5280_, v___x_5281_, v___x_5292_, v_a_5271_, v___x_5294_, v___x_5296_, v___x_5298_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v___x_5299_);
v___x_5301_ = v___x_5274_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5299_);
lean_ctor_set(v_reuseFailAlloc_5302_, 1, v_a_5272_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_dec(v_type_5261_);
v_a_5304_ = lean_ctor_get(v___x_5270_, 0);
v_a_5305_ = lean_ctor_get(v___x_5270_, 1);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5270_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_inc(v_a_5304_);
lean_dec(v___x_5270_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5304_);
lean_ctor_set(v_reuseFailAlloc_5311_, 1, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5313_, lean_object* v_type_5314_, lean_object* v_ofInterpFn_5315_, lean_object* v_ofLitFn_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5313_, v_type_5314_, v_ofInterpFn_5315_, v_ofLitFn_5316_, v_a_5317_, v_a_5318_);
lean_dec_ref(v_a_5317_);
lean_dec(v_interpStr_5313_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5320_){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5321_ = lean_unsigned_to_nat(1u);
v___x_5322_ = l_Lean_Syntax_getArg(v_stx_5320_, v___x_5321_);
if (lean_obj_tag(v___x_5322_) == 2)
{
lean_object* v_val_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v_val_5323_ = lean_ctor_get(v___x_5322_, 1);
lean_inc_ref(v_val_5323_);
lean_dec_ref_known(v___x_5322_, 2);
v___x_5324_ = lean_unsigned_to_nat(0u);
v___x_5325_ = lean_string_utf8_byte_size(v_val_5323_);
v___x_5326_ = lean_unsigned_to_nat(2u);
v___x_5327_ = lean_string_pos_sub(v___x_5325_, v___x_5326_);
v___x_5328_ = lean_string_utf8_extract(v_val_5323_, v___x_5324_, v___x_5327_);
lean_dec(v___x_5327_);
lean_dec_ref(v_val_5323_);
return v___x_5328_;
}
else
{
lean_object* v___x_5329_; 
lean_dec(v___x_5322_);
v___x_5329_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Lean_TSyntax_getDocString(v_stx_5330_);
lean_dec(v_stx_5330_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5350_, lean_object* v_prec_5351_){
_start:
{
lean_object* v___y_5353_; lean_object* v___y_5360_; lean_object* v___y_5367_; lean_object* v___y_5374_; lean_object* v___y_5381_; lean_object* v___y_5388_; 
switch(v_x_5350_)
{
case 0:
{
lean_object* v___x_5394_; uint8_t v___x_5395_; 
v___x_5394_ = lean_unsigned_to_nat(1024u);
v___x_5395_ = lean_nat_dec_le(v___x_5394_, v_prec_5351_);
if (v___x_5395_ == 0)
{
lean_object* v___x_5396_; 
v___x_5396_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5353_ = v___x_5396_;
goto v___jp_5352_;
}
else
{
lean_object* v___x_5397_; 
v___x_5397_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5353_ = v___x_5397_;
goto v___jp_5352_;
}
}
case 1:
{
lean_object* v___x_5398_; uint8_t v___x_5399_; 
v___x_5398_ = lean_unsigned_to_nat(1024u);
v___x_5399_ = lean_nat_dec_le(v___x_5398_, v_prec_5351_);
if (v___x_5399_ == 0)
{
lean_object* v___x_5400_; 
v___x_5400_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5360_ = v___x_5400_;
goto v___jp_5359_;
}
else
{
lean_object* v___x_5401_; 
v___x_5401_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5360_ = v___x_5401_;
goto v___jp_5359_;
}
}
case 2:
{
lean_object* v___x_5402_; uint8_t v___x_5403_; 
v___x_5402_ = lean_unsigned_to_nat(1024u);
v___x_5403_ = lean_nat_dec_le(v___x_5402_, v_prec_5351_);
if (v___x_5403_ == 0)
{
lean_object* v___x_5404_; 
v___x_5404_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5367_ = v___x_5404_;
goto v___jp_5366_;
}
else
{
lean_object* v___x_5405_; 
v___x_5405_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5367_ = v___x_5405_;
goto v___jp_5366_;
}
}
case 3:
{
lean_object* v___x_5406_; uint8_t v___x_5407_; 
v___x_5406_ = lean_unsigned_to_nat(1024u);
v___x_5407_ = lean_nat_dec_le(v___x_5406_, v_prec_5351_);
if (v___x_5407_ == 0)
{
lean_object* v___x_5408_; 
v___x_5408_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5374_ = v___x_5408_;
goto v___jp_5373_;
}
else
{
lean_object* v___x_5409_; 
v___x_5409_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5374_ = v___x_5409_;
goto v___jp_5373_;
}
}
case 4:
{
lean_object* v___x_5410_; uint8_t v___x_5411_; 
v___x_5410_ = lean_unsigned_to_nat(1024u);
v___x_5411_ = lean_nat_dec_le(v___x_5410_, v_prec_5351_);
if (v___x_5411_ == 0)
{
lean_object* v___x_5412_; 
v___x_5412_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5381_ = v___x_5412_;
goto v___jp_5380_;
}
else
{
lean_object* v___x_5413_; 
v___x_5413_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5381_ = v___x_5413_;
goto v___jp_5380_;
}
}
default: 
{
lean_object* v___x_5414_; uint8_t v___x_5415_; 
v___x_5414_ = lean_unsigned_to_nat(1024u);
v___x_5415_ = lean_nat_dec_le(v___x_5414_, v_prec_5351_);
if (v___x_5415_ == 0)
{
lean_object* v___x_5416_; 
v___x_5416_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5388_ = v___x_5416_;
goto v___jp_5387_;
}
else
{
lean_object* v___x_5417_; 
v___x_5417_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5388_ = v___x_5417_;
goto v___jp_5387_;
}
}
}
v___jp_5352_:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; uint8_t v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5354_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5353_);
v___x_5355_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___y_5353_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
v___x_5356_ = 0;
v___x_5357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5357_, 0, v___x_5355_);
lean_ctor_set_uint8(v___x_5357_, sizeof(void*)*1, v___x_5356_);
v___x_5358_ = l_Repr_addAppParen(v___x_5357_, v_prec_5351_);
return v___x_5358_;
}
v___jp_5359_:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; uint8_t v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5361_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5360_);
v___x_5362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5362_, 0, v___y_5360_);
lean_ctor_set(v___x_5362_, 1, v___x_5361_);
v___x_5363_ = 0;
v___x_5364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5364_, 0, v___x_5362_);
lean_ctor_set_uint8(v___x_5364_, sizeof(void*)*1, v___x_5363_);
v___x_5365_ = l_Repr_addAppParen(v___x_5364_, v_prec_5351_);
return v___x_5365_;
}
v___jp_5366_:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; uint8_t v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; 
v___x_5368_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5367_);
v___x_5369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___y_5367_);
lean_ctor_set(v___x_5369_, 1, v___x_5368_);
v___x_5370_ = 0;
v___x_5371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5371_, 0, v___x_5369_);
lean_ctor_set_uint8(v___x_5371_, sizeof(void*)*1, v___x_5370_);
v___x_5372_ = l_Repr_addAppParen(v___x_5371_, v_prec_5351_);
return v___x_5372_;
}
v___jp_5373_:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; 
v___x_5375_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5374_);
v___x_5376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5376_, 0, v___y_5374_);
lean_ctor_set(v___x_5376_, 1, v___x_5375_);
v___x_5377_ = 0;
v___x_5378_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5378_, 0, v___x_5376_);
lean_ctor_set_uint8(v___x_5378_, sizeof(void*)*1, v___x_5377_);
v___x_5379_ = l_Repr_addAppParen(v___x_5378_, v_prec_5351_);
return v___x_5379_;
}
v___jp_5380_:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; uint8_t v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5382_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5381_);
v___x_5383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___y_5381_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = 0;
v___x_5385_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5385_, 0, v___x_5383_);
lean_ctor_set_uint8(v___x_5385_, sizeof(void*)*1, v___x_5384_);
v___x_5386_ = l_Repr_addAppParen(v___x_5385_, v_prec_5351_);
return v___x_5386_;
}
v___jp_5387_:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5389_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5388_);
v___x_5390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5390_, 0, v___y_5388_);
lean_ctor_set(v___x_5390_, 1, v___x_5389_);
v___x_5391_ = 0;
v___x_5392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5392_, 0, v___x_5390_);
lean_ctor_set_uint8(v___x_5392_, sizeof(void*)*1, v___x_5391_);
v___x_5393_ = l_Repr_addAppParen(v___x_5392_, v_prec_5351_);
return v___x_5393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5418_, lean_object* v_prec_5419_){
_start:
{
uint8_t v_x_329__boxed_5420_; lean_object* v_res_5421_; 
v_x_329__boxed_5420_ = lean_unbox(v_x_5418_);
v_res_5421_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5420_, v_prec_5419_);
lean_dec(v_prec_5419_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5433_, lean_object* v_prec_5434_){
_start:
{
lean_object* v___y_5436_; lean_object* v___y_5443_; lean_object* v___y_5450_; 
switch(v_x_5433_)
{
case 0:
{
lean_object* v___x_5456_; uint8_t v___x_5457_; 
v___x_5456_ = lean_unsigned_to_nat(1024u);
v___x_5457_ = lean_nat_dec_le(v___x_5456_, v_prec_5434_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5436_ = v___x_5458_;
goto v___jp_5435_;
}
else
{
lean_object* v___x_5459_; 
v___x_5459_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5436_ = v___x_5459_;
goto v___jp_5435_;
}
}
case 1:
{
lean_object* v___x_5460_; uint8_t v___x_5461_; 
v___x_5460_ = lean_unsigned_to_nat(1024u);
v___x_5461_ = lean_nat_dec_le(v___x_5460_, v_prec_5434_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5462_; 
v___x_5462_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5443_ = v___x_5462_;
goto v___jp_5442_;
}
else
{
lean_object* v___x_5463_; 
v___x_5463_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5443_ = v___x_5463_;
goto v___jp_5442_;
}
}
default: 
{
lean_object* v___x_5464_; uint8_t v___x_5465_; 
v___x_5464_ = lean_unsigned_to_nat(1024u);
v___x_5465_ = lean_nat_dec_le(v___x_5464_, v_prec_5434_);
if (v___x_5465_ == 0)
{
lean_object* v___x_5466_; 
v___x_5466_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5450_ = v___x_5466_;
goto v___jp_5449_;
}
else
{
lean_object* v___x_5467_; 
v___x_5467_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5450_ = v___x_5467_;
goto v___jp_5449_;
}
}
}
v___jp_5435_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; uint8_t v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5437_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5436_);
v___x_5438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5438_, 0, v___y_5436_);
lean_ctor_set(v___x_5438_, 1, v___x_5437_);
v___x_5439_ = 0;
v___x_5440_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5440_, 0, v___x_5438_);
lean_ctor_set_uint8(v___x_5440_, sizeof(void*)*1, v___x_5439_);
v___x_5441_ = l_Repr_addAppParen(v___x_5440_, v_prec_5434_);
return v___x_5441_;
}
v___jp_5442_:
{
lean_object* v___x_5444_; lean_object* v___x_5445_; uint8_t v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5444_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5443_);
v___x_5445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___y_5443_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = 0;
v___x_5447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5447_, 0, v___x_5445_);
lean_ctor_set_uint8(v___x_5447_, sizeof(void*)*1, v___x_5446_);
v___x_5448_ = l_Repr_addAppParen(v___x_5447_, v_prec_5434_);
return v___x_5448_;
}
v___jp_5449_:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; uint8_t v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5451_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5450_);
v___x_5452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5452_, 0, v___y_5450_);
lean_ctor_set(v___x_5452_, 1, v___x_5451_);
v___x_5453_ = 0;
v___x_5454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5454_, 0, v___x_5452_);
lean_ctor_set_uint8(v___x_5454_, sizeof(void*)*1, v___x_5453_);
v___x_5455_ = l_Repr_addAppParen(v___x_5454_, v_prec_5434_);
return v___x_5455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5468_, lean_object* v_prec_5469_){
_start:
{
uint8_t v_x_167__boxed_5470_; lean_object* v_res_5471_; 
v_x_167__boxed_5470_ = lean_unbox(v_x_5468_);
v_res_5471_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5470_, v_prec_5469_);
lean_dec(v_prec_5469_);
return v_res_5471_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5483_ = lean_unsigned_to_nat(8u);
v___x_5484_ = lean_nat_to_int(v___x_5483_);
return v___x_5484_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_unsigned_to_nat(13u);
v___x_5495_ = lean_nat_to_int(v___x_5494_);
return v___x_5495_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5505_ = lean_unsigned_to_nat(10u);
v___x_5506_ = lean_nat_to_int(v___x_5505_);
return v___x_5506_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = lean_unsigned_to_nat(14u);
v___x_5511_ = lean_nat_to_int(v___x_5510_);
return v___x_5511_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = lean_unsigned_to_nat(19u);
v___x_5516_ = lean_nat_to_int(v___x_5515_);
return v___x_5516_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
v___x_5520_ = lean_unsigned_to_nat(20u);
v___x_5521_ = lean_nat_to_int(v___x_5520_);
return v___x_5521_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5528_; lean_object* v___x_5529_; 
v___x_5528_ = lean_unsigned_to_nat(9u);
v___x_5529_ = lean_nat_to_int(v___x_5528_);
return v___x_5529_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_unsigned_to_nat(12u);
v___x_5537_ = lean_nat_to_int(v___x_5536_);
return v___x_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5544_){
_start:
{
uint8_t v_zeta_5545_; uint8_t v_beta_5546_; uint8_t v_eta_5547_; uint8_t v_etaStruct_5548_; uint8_t v_iota_5549_; uint8_t v_proj_5550_; uint8_t v_decide_5551_; uint8_t v_autoUnfold_5552_; uint8_t v_failIfUnchanged_5553_; uint8_t v_unfoldPartialApp_5554_; uint8_t v_zetaDelta_5555_; uint8_t v_index_5556_; uint8_t v_zetaUnused_5557_; uint8_t v_zetaHave_5558_; uint8_t v_locals_5559_; uint8_t v_instances_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; uint8_t v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v_zeta_5545_ = lean_ctor_get_uint8(v_x_5544_, 0);
v_beta_5546_ = lean_ctor_get_uint8(v_x_5544_, 1);
v_eta_5547_ = lean_ctor_get_uint8(v_x_5544_, 2);
v_etaStruct_5548_ = lean_ctor_get_uint8(v_x_5544_, 3);
v_iota_5549_ = lean_ctor_get_uint8(v_x_5544_, 4);
v_proj_5550_ = lean_ctor_get_uint8(v_x_5544_, 5);
v_decide_5551_ = lean_ctor_get_uint8(v_x_5544_, 6);
v_autoUnfold_5552_ = lean_ctor_get_uint8(v_x_5544_, 7);
v_failIfUnchanged_5553_ = lean_ctor_get_uint8(v_x_5544_, 8);
v_unfoldPartialApp_5554_ = lean_ctor_get_uint8(v_x_5544_, 9);
v_zetaDelta_5555_ = lean_ctor_get_uint8(v_x_5544_, 10);
v_index_5556_ = lean_ctor_get_uint8(v_x_5544_, 11);
v_zetaUnused_5557_ = lean_ctor_get_uint8(v_x_5544_, 12);
v_zetaHave_5558_ = lean_ctor_get_uint8(v_x_5544_, 13);
v_locals_5559_ = lean_ctor_get_uint8(v_x_5544_, 14);
v_instances_5560_ = lean_ctor_get_uint8(v_x_5544_, 15);
v___x_5561_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5562_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5563_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5564_ = lean_unsigned_to_nat(0u);
v___x_5565_ = l_Bool_repr___redArg(v_zeta_5545_);
v___x_5566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5563_);
lean_ctor_set(v___x_5566_, 1, v___x_5565_);
v___x_5567_ = 0;
v___x_5568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5568_, 0, v___x_5566_);
lean_ctor_set_uint8(v___x_5568_, sizeof(void*)*1, v___x_5567_);
v___x_5569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5562_);
lean_ctor_set(v___x_5569_, 1, v___x_5568_);
v___x_5570_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5569_);
lean_ctor_set(v___x_5571_, 1, v___x_5570_);
v___x_5572_ = lean_box(1);
v___x_5573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5571_);
lean_ctor_set(v___x_5573_, 1, v___x_5572_);
v___x_5574_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5573_);
lean_ctor_set(v___x_5575_, 1, v___x_5574_);
v___x_5576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5575_);
lean_ctor_set(v___x_5576_, 1, v___x_5561_);
v___x_5577_ = l_Bool_repr___redArg(v_beta_5546_);
v___x_5578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5578_, 0, v___x_5563_);
lean_ctor_set(v___x_5578_, 1, v___x_5577_);
v___x_5579_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
lean_ctor_set_uint8(v___x_5579_, sizeof(void*)*1, v___x_5567_);
v___x_5580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5576_);
lean_ctor_set(v___x_5580_, 1, v___x_5579_);
v___x_5581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5581_, 0, v___x_5580_);
lean_ctor_set(v___x_5581_, 1, v___x_5570_);
v___x_5582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
lean_ctor_set(v___x_5582_, 1, v___x_5572_);
v___x_5583_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5582_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
lean_ctor_set(v___x_5585_, 1, v___x_5561_);
v___x_5586_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5587_ = l_Bool_repr___redArg(v_eta_5547_);
v___x_5588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5586_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
v___x_5589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
lean_ctor_set_uint8(v___x_5589_, sizeof(void*)*1, v___x_5567_);
v___x_5590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5590_, 0, v___x_5585_);
lean_ctor_set(v___x_5590_, 1, v___x_5589_);
v___x_5591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5590_);
lean_ctor_set(v___x_5591_, 1, v___x_5570_);
v___x_5592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5591_);
lean_ctor_set(v___x_5592_, 1, v___x_5572_);
v___x_5593_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5594_, 0, v___x_5592_);
lean_ctor_set(v___x_5594_, 1, v___x_5593_);
v___x_5595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5594_);
lean_ctor_set(v___x_5595_, 1, v___x_5561_);
v___x_5596_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5597_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5548_, v___x_5564_);
v___x_5598_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5598_, 0, v___x_5596_);
lean_ctor_set(v___x_5598_, 1, v___x_5597_);
v___x_5599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
lean_ctor_set_uint8(v___x_5599_, sizeof(void*)*1, v___x_5567_);
v___x_5600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5600_, 0, v___x_5595_);
lean_ctor_set(v___x_5600_, 1, v___x_5599_);
v___x_5601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5601_, 0, v___x_5600_);
lean_ctor_set(v___x_5601_, 1, v___x_5570_);
v___x_5602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5602_, 0, v___x_5601_);
lean_ctor_set(v___x_5602_, 1, v___x_5572_);
v___x_5603_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5602_);
lean_ctor_set(v___x_5604_, 1, v___x_5603_);
v___x_5605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
lean_ctor_set(v___x_5605_, 1, v___x_5561_);
v___x_5606_ = l_Bool_repr___redArg(v_iota_5549_);
v___x_5607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5563_);
lean_ctor_set(v___x_5607_, 1, v___x_5606_);
v___x_5608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5608_, 0, v___x_5607_);
lean_ctor_set_uint8(v___x_5608_, sizeof(void*)*1, v___x_5567_);
v___x_5609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5605_);
lean_ctor_set(v___x_5609_, 1, v___x_5608_);
v___x_5610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
lean_ctor_set(v___x_5610_, 1, v___x_5570_);
v___x_5611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5610_);
lean_ctor_set(v___x_5611_, 1, v___x_5572_);
v___x_5612_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5611_);
lean_ctor_set(v___x_5613_, 1, v___x_5612_);
v___x_5614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5614_, 0, v___x_5613_);
lean_ctor_set(v___x_5614_, 1, v___x_5561_);
v___x_5615_ = l_Bool_repr___redArg(v_proj_5550_);
v___x_5616_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5563_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5617_, 0, v___x_5616_);
lean_ctor_set_uint8(v___x_5617_, sizeof(void*)*1, v___x_5567_);
v___x_5618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5614_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
lean_ctor_set(v___x_5619_, 1, v___x_5570_);
v___x_5620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5619_);
lean_ctor_set(v___x_5620_, 1, v___x_5572_);
v___x_5621_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5620_);
lean_ctor_set(v___x_5622_, 1, v___x_5621_);
v___x_5623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set(v___x_5623_, 1, v___x_5561_);
v___x_5624_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5625_ = l_Bool_repr___redArg(v_decide_5551_);
v___x_5626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5624_);
lean_ctor_set(v___x_5626_, 1, v___x_5625_);
v___x_5627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set_uint8(v___x_5627_, sizeof(void*)*1, v___x_5567_);
v___x_5628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5623_);
lean_ctor_set(v___x_5628_, 1, v___x_5627_);
v___x_5629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5628_);
lean_ctor_set(v___x_5629_, 1, v___x_5570_);
v___x_5630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5629_);
lean_ctor_set(v___x_5630_, 1, v___x_5572_);
v___x_5631_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5630_);
lean_ctor_set(v___x_5632_, 1, v___x_5631_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v___x_5561_);
v___x_5634_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5635_ = l_Bool_repr___redArg(v_autoUnfold_5552_);
v___x_5636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set_uint8(v___x_5637_, sizeof(void*)*1, v___x_5567_);
v___x_5638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5633_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
lean_ctor_set(v___x_5639_, 1, v___x_5570_);
v___x_5640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5639_);
lean_ctor_set(v___x_5640_, 1, v___x_5572_);
v___x_5641_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5640_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
lean_ctor_set(v___x_5643_, 1, v___x_5561_);
v___x_5644_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5645_ = l_Bool_repr___redArg(v_failIfUnchanged_5553_);
v___x_5646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5644_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
v___x_5647_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set_uint8(v___x_5647_, sizeof(void*)*1, v___x_5567_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5643_);
lean_ctor_set(v___x_5648_, 1, v___x_5647_);
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5648_);
lean_ctor_set(v___x_5649_, 1, v___x_5570_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set(v___x_5650_, 1, v___x_5572_);
v___x_5651_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5650_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5561_);
v___x_5654_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5655_ = l_Bool_repr___redArg(v_unfoldPartialApp_5554_);
v___x_5656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set_uint8(v___x_5657_, sizeof(void*)*1, v___x_5567_);
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5653_);
lean_ctor_set(v___x_5658_, 1, v___x_5657_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set(v___x_5659_, 1, v___x_5570_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set(v___x_5660_, 1, v___x_5572_);
v___x_5661_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5660_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___x_5561_);
v___x_5664_ = l_Bool_repr___redArg(v_zetaDelta_5555_);
v___x_5665_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5596_);
lean_ctor_set(v___x_5665_, 1, v___x_5664_);
v___x_5666_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
lean_ctor_set_uint8(v___x_5666_, sizeof(void*)*1, v___x_5567_);
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5663_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___x_5570_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set(v___x_5669_, 1, v___x_5572_);
v___x_5670_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5669_);
lean_ctor_set(v___x_5671_, 1, v___x_5670_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
lean_ctor_set(v___x_5672_, 1, v___x_5561_);
v___x_5673_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5674_ = l_Bool_repr___redArg(v_index_5556_);
v___x_5675_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5673_);
lean_ctor_set(v___x_5675_, 1, v___x_5674_);
v___x_5676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
lean_ctor_set_uint8(v___x_5676_, sizeof(void*)*1, v___x_5567_);
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5672_);
lean_ctor_set(v___x_5677_, 1, v___x_5676_);
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set(v___x_5678_, 1, v___x_5570_);
v___x_5679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set(v___x_5679_, 1, v___x_5572_);
v___x_5680_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5679_);
lean_ctor_set(v___x_5681_, 1, v___x_5680_);
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set(v___x_5682_, 1, v___x_5561_);
v___x_5683_ = l_Bool_repr___redArg(v_zetaUnused_5557_);
v___x_5684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5634_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set_uint8(v___x_5685_, sizeof(void*)*1, v___x_5567_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5682_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5686_);
lean_ctor_set(v___x_5687_, 1, v___x_5570_);
v___x_5688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set(v___x_5688_, 1, v___x_5572_);
v___x_5689_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5688_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5561_);
v___x_5692_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5693_ = l_Bool_repr___redArg(v_zetaHave_5558_);
v___x_5694_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set_uint8(v___x_5695_, sizeof(void*)*1, v___x_5567_);
v___x_5696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5691_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
lean_ctor_set(v___x_5697_, 1, v___x_5570_);
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5697_);
lean_ctor_set(v___x_5698_, 1, v___x_5572_);
v___x_5699_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5698_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
lean_ctor_set(v___x_5701_, 1, v___x_5561_);
v___x_5702_ = l_Bool_repr___redArg(v_locals_5559_);
v___x_5703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5624_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
v___x_5704_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5704_, 0, v___x_5703_);
lean_ctor_set_uint8(v___x_5704_, sizeof(void*)*1, v___x_5567_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5701_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
lean_ctor_set(v___x_5706_, 1, v___x_5570_);
v___x_5707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
lean_ctor_set(v___x_5707_, 1, v___x_5572_);
v___x_5708_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5707_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set(v___x_5710_, 1, v___x_5561_);
v___x_5711_ = l_Bool_repr___redArg(v_instances_5560_);
v___x_5712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5596_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*1, v___x_5567_);
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5710_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5716_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
lean_ctor_set(v___x_5717_, 1, v___x_5714_);
v___x_5718_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5717_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
v___x_5720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5715_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set_uint8(v___x_5721_, sizeof(void*)*1, v___x_5567_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5722_);
lean_dec_ref(v_x_5722_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5724_, lean_object* v_prec_5725_){
_start:
{
lean_object* v___x_5726_; 
v___x_5726_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5724_);
return v___x_5726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5727_, lean_object* v_prec_5728_){
_start:
{
lean_object* v_res_5729_; 
v_res_5729_ = l_Lean_Meta_instReprConfig_repr(v_x_5727_, v_prec_5728_);
lean_dec(v_prec_5728_);
lean_dec_ref(v_x_5727_);
return v_res_5729_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5737_, lean_object* v_x_5738_){
_start:
{
if (lean_obj_tag(v_x_5737_) == 0)
{
lean_object* v___x_5739_; 
v___x_5739_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5739_;
}
else
{
lean_object* v_val_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5751_; 
v_val_5740_ = lean_ctor_get(v_x_5737_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v_x_5737_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5742_ = v_x_5737_;
v_isShared_5743_ = v_isSharedCheck_5751_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_val_5740_);
lean_dec(v_x_5737_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5751_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5747_; 
v___x_5744_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5745_ = l_Nat_reprFast(v_val_5740_);
if (v_isShared_5743_ == 0)
{
lean_ctor_set_tag(v___x_5742_, 3);
lean_ctor_set(v___x_5742_, 0, v___x_5745_);
v___x_5747_ = v___x_5742_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v___x_5745_);
v___x_5747_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5744_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v___x_5749_ = l_Repr_addAppParen(v___x_5748_, v_x_5738_);
return v___x_5749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5752_, lean_object* v_x_5753_){
_start:
{
lean_object* v_res_5754_; 
v_res_5754_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5752_, v_x_5753_);
lean_dec(v_x_5753_);
return v_res_5754_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___x_5767_ = lean_unsigned_to_nat(21u);
v___x_5768_ = lean_nat_to_int(v___x_5767_);
return v___x_5768_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5775_; lean_object* v___x_5776_; 
v___x_5775_ = lean_unsigned_to_nat(11u);
v___x_5776_ = lean_nat_to_int(v___x_5775_);
return v___x_5776_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5792_; lean_object* v___x_5793_; 
v___x_5792_ = lean_unsigned_to_nat(23u);
v___x_5793_ = lean_nat_to_int(v___x_5792_);
return v___x_5793_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5797_ = lean_unsigned_to_nat(16u);
v___x_5798_ = lean_nat_to_int(v___x_5797_);
return v___x_5798_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5805_; lean_object* v___x_5806_; 
v___x_5805_ = lean_unsigned_to_nat(15u);
v___x_5806_ = lean_nat_to_int(v___x_5805_);
return v___x_5806_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = lean_unsigned_to_nat(17u);
v___x_5814_ = lean_nat_to_int(v___x_5813_);
return v___x_5814_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = lean_unsigned_to_nat(18u);
v___x_5822_ = lean_nat_to_int(v___x_5821_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5823_){
_start:
{
lean_object* v_maxSteps_5824_; lean_object* v_maxDischargeDepth_5825_; uint8_t v_contextual_5826_; uint8_t v_memoize_5827_; uint8_t v_singlePass_5828_; uint8_t v_zeta_5829_; uint8_t v_beta_5830_; uint8_t v_eta_5831_; uint8_t v_etaStruct_5832_; uint8_t v_iota_5833_; uint8_t v_proj_5834_; uint8_t v_decide_5835_; uint8_t v_arith_5836_; uint8_t v_autoUnfold_5837_; uint8_t v_dsimp_5838_; uint8_t v_failIfUnchanged_5839_; uint8_t v_ground_5840_; uint8_t v_unfoldPartialApp_5841_; uint8_t v_zetaDelta_5842_; uint8_t v_index_5843_; uint8_t v_implicitDefEqProofs_5844_; uint8_t v_zetaUnused_5845_; uint8_t v_catchRuntime_5846_; uint8_t v_zetaHave_5847_; uint8_t v_letToHave_5848_; uint8_t v_congrConsts_5849_; uint8_t v_bitVecOfNat_5850_; uint8_t v_warnExponents_5851_; uint8_t v_suggestions_5852_; lean_object* v_maxSuggestions_5853_; uint8_t v_locals_5854_; uint8_t v_instances_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; uint8_t v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; 
v_maxSteps_5824_ = lean_ctor_get(v_x_5823_, 0);
lean_inc(v_maxSteps_5824_);
v_maxDischargeDepth_5825_ = lean_ctor_get(v_x_5823_, 1);
lean_inc(v_maxDischargeDepth_5825_);
v_contextual_5826_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3);
v_memoize_5827_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 1);
v_singlePass_5828_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 2);
v_zeta_5829_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 3);
v_beta_5830_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 4);
v_eta_5831_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 5);
v_etaStruct_5832_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 6);
v_iota_5833_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 7);
v_proj_5834_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 8);
v_decide_5835_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 9);
v_arith_5836_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 10);
v_autoUnfold_5837_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 11);
v_dsimp_5838_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5839_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 13);
v_ground_5840_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5841_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 15);
v_zetaDelta_5842_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 16);
v_index_5843_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5844_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 18);
v_zetaUnused_5845_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 19);
v_catchRuntime_5846_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 20);
v_zetaHave_5847_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 21);
v_letToHave_5848_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 22);
v_congrConsts_5849_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5850_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 24);
v_warnExponents_5851_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 25);
v_suggestions_5852_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 26);
v_maxSuggestions_5853_ = lean_ctor_get(v_x_5823_, 2);
lean_inc(v_maxSuggestions_5853_);
v_locals_5854_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 27);
v_instances_5855_ = lean_ctor_get_uint8(v_x_5823_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5823_);
v___x_5856_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5857_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5858_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5859_ = l_Nat_reprFast(v_maxSteps_5824_);
v___x_5860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5859_);
v___x_5861_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5858_);
lean_ctor_set(v___x_5861_, 1, v___x_5860_);
v___x_5862_ = 0;
v___x_5863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5863_, 0, v___x_5861_);
lean_ctor_set_uint8(v___x_5863_, sizeof(void*)*1, v___x_5862_);
v___x_5864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5857_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
v___x_5865_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5864_);
lean_ctor_set(v___x_5866_, 1, v___x_5865_);
v___x_5867_ = lean_box(1);
v___x_5868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5866_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
v___x_5869_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5870_, 0, v___x_5868_);
lean_ctor_set(v___x_5870_, 1, v___x_5869_);
v___x_5871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5870_);
lean_ctor_set(v___x_5871_, 1, v___x_5856_);
v___x_5872_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5873_ = l_Nat_reprFast(v_maxDischargeDepth_5825_);
v___x_5874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5874_, 0, v___x_5873_);
v___x_5875_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5872_);
lean_ctor_set(v___x_5875_, 1, v___x_5874_);
v___x_5876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5876_, 0, v___x_5875_);
lean_ctor_set_uint8(v___x_5876_, sizeof(void*)*1, v___x_5862_);
v___x_5877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5877_, 0, v___x_5871_);
lean_ctor_set(v___x_5877_, 1, v___x_5876_);
v___x_5878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
lean_ctor_set(v___x_5878_, 1, v___x_5865_);
v___x_5879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5879_, 0, v___x_5878_);
lean_ctor_set(v___x_5879_, 1, v___x_5867_);
v___x_5880_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5879_);
lean_ctor_set(v___x_5881_, 1, v___x_5880_);
v___x_5882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5881_);
lean_ctor_set(v___x_5882_, 1, v___x_5856_);
v___x_5883_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5884_ = lean_unsigned_to_nat(0u);
v___x_5885_ = l_Bool_repr___redArg(v_contextual_5826_);
v___x_5886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5886_, 0, v___x_5883_);
lean_ctor_set(v___x_5886_, 1, v___x_5885_);
v___x_5887_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5887_, 0, v___x_5886_);
lean_ctor_set_uint8(v___x_5887_, sizeof(void*)*1, v___x_5862_);
v___x_5888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5882_);
lean_ctor_set(v___x_5888_, 1, v___x_5887_);
v___x_5889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5888_);
lean_ctor_set(v___x_5889_, 1, v___x_5865_);
v___x_5890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5889_);
lean_ctor_set(v___x_5890_, 1, v___x_5867_);
v___x_5891_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5890_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5892_);
lean_ctor_set(v___x_5893_, 1, v___x_5856_);
v___x_5894_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5895_ = l_Bool_repr___redArg(v_memoize_5827_);
v___x_5896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5894_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
v___x_5897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5897_, 0, v___x_5896_);
lean_ctor_set_uint8(v___x_5897_, sizeof(void*)*1, v___x_5862_);
v___x_5898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5893_);
lean_ctor_set(v___x_5898_, 1, v___x_5897_);
v___x_5899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5898_);
lean_ctor_set(v___x_5899_, 1, v___x_5865_);
v___x_5900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5899_);
lean_ctor_set(v___x_5900_, 1, v___x_5867_);
v___x_5901_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5900_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5902_);
lean_ctor_set(v___x_5903_, 1, v___x_5856_);
v___x_5904_ = l_Bool_repr___redArg(v_singlePass_5828_);
v___x_5905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5883_);
lean_ctor_set(v___x_5905_, 1, v___x_5904_);
v___x_5906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5906_, 0, v___x_5905_);
lean_ctor_set_uint8(v___x_5906_, sizeof(void*)*1, v___x_5862_);
v___x_5907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5903_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5907_);
lean_ctor_set(v___x_5908_, 1, v___x_5865_);
v___x_5909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5908_);
lean_ctor_set(v___x_5909_, 1, v___x_5867_);
v___x_5910_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5909_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
lean_ctor_set(v___x_5912_, 1, v___x_5856_);
v___x_5913_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5914_ = l_Bool_repr___redArg(v_zeta_5829_);
v___x_5915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5916_, 0, v___x_5915_);
lean_ctor_set_uint8(v___x_5916_, sizeof(void*)*1, v___x_5862_);
v___x_5917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5912_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
v___x_5918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
lean_ctor_set(v___x_5918_, 1, v___x_5865_);
v___x_5919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
lean_ctor_set(v___x_5919_, 1, v___x_5867_);
v___x_5920_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5919_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
lean_ctor_set(v___x_5922_, 1, v___x_5856_);
v___x_5923_ = l_Bool_repr___redArg(v_beta_5830_);
v___x_5924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5913_);
lean_ctor_set(v___x_5924_, 1, v___x_5923_);
v___x_5925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5925_, 0, v___x_5924_);
lean_ctor_set_uint8(v___x_5925_, sizeof(void*)*1, v___x_5862_);
v___x_5926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5922_);
lean_ctor_set(v___x_5926_, 1, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5926_);
lean_ctor_set(v___x_5927_, 1, v___x_5865_);
v___x_5928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set(v___x_5928_, 1, v___x_5867_);
v___x_5929_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5928_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5856_);
v___x_5932_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5933_ = l_Bool_repr___redArg(v_eta_5831_);
v___x_5934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set_uint8(v___x_5935_, sizeof(void*)*1, v___x_5862_);
v___x_5936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5931_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5936_);
lean_ctor_set(v___x_5937_, 1, v___x_5865_);
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
lean_ctor_set(v___x_5938_, 1, v___x_5867_);
v___x_5939_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5938_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5856_);
v___x_5942_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5943_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5832_, v___x_5884_);
v___x_5944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set_uint8(v___x_5945_, sizeof(void*)*1, v___x_5862_);
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5941_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set(v___x_5947_, 1, v___x_5865_);
v___x_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5947_);
lean_ctor_set(v___x_5948_, 1, v___x_5867_);
v___x_5949_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5948_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set(v___x_5951_, 1, v___x_5856_);
v___x_5952_ = l_Bool_repr___redArg(v_iota_5833_);
v___x_5953_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5913_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v___x_5954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set_uint8(v___x_5954_, sizeof(void*)*1, v___x_5862_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5951_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5955_);
lean_ctor_set(v___x_5956_, 1, v___x_5865_);
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
lean_ctor_set(v___x_5957_, 1, v___x_5867_);
v___x_5958_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5957_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5959_);
lean_ctor_set(v___x_5960_, 1, v___x_5856_);
v___x_5961_ = l_Bool_repr___redArg(v_proj_5834_);
v___x_5962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5913_);
lean_ctor_set(v___x_5962_, 1, v___x_5961_);
v___x_5963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
lean_ctor_set_uint8(v___x_5963_, sizeof(void*)*1, v___x_5862_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5960_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set(v___x_5965_, 1, v___x_5865_);
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set(v___x_5966_, 1, v___x_5867_);
v___x_5967_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5856_);
v___x_5970_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5971_ = l_Bool_repr___redArg(v_decide_5835_);
v___x_5972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
v___x_5973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set_uint8(v___x_5973_, sizeof(void*)*1, v___x_5862_);
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5969_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
lean_ctor_set(v___x_5975_, 1, v___x_5865_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set(v___x_5976_, 1, v___x_5867_);
v___x_5977_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5976_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5856_);
v___x_5980_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5981_ = l_Bool_repr___redArg(v_arith_5836_);
v___x_5982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5980_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
lean_ctor_set_uint8(v___x_5983_, sizeof(void*)*1, v___x_5862_);
v___x_5984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5979_);
lean_ctor_set(v___x_5984_, 1, v___x_5983_);
v___x_5985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
lean_ctor_set(v___x_5985_, 1, v___x_5865_);
v___x_5986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5985_);
lean_ctor_set(v___x_5986_, 1, v___x_5867_);
v___x_5987_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5986_);
lean_ctor_set(v___x_5988_, 1, v___x_5987_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5988_);
lean_ctor_set(v___x_5989_, 1, v___x_5856_);
v___x_5990_ = l_Bool_repr___redArg(v_autoUnfold_5837_);
v___x_5991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5883_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5992_, 0, v___x_5991_);
lean_ctor_set_uint8(v___x_5992_, sizeof(void*)*1, v___x_5862_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5989_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set(v___x_5994_, 1, v___x_5865_);
v___x_5995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5994_);
lean_ctor_set(v___x_5995_, 1, v___x_5867_);
v___x_5996_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5995_);
lean_ctor_set(v___x_5997_, 1, v___x_5996_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5997_);
lean_ctor_set(v___x_5998_, 1, v___x_5856_);
v___x_5999_ = l_Bool_repr___redArg(v_dsimp_5838_);
v___x_6000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5980_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v___x_6001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set_uint8(v___x_6001_, sizeof(void*)*1, v___x_5862_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_5998_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v___x_5865_);
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set(v___x_6004_, 1, v___x_5867_);
v___x_6005_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6004_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5856_);
v___x_6008_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6009_ = l_Bool_repr___redArg(v_failIfUnchanged_5839_);
v___x_6010_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6008_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set_uint8(v___x_6011_, sizeof(void*)*1, v___x_5862_);
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6007_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set(v___x_6013_, 1, v___x_5865_);
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set(v___x_6014_, 1, v___x_5867_);
v___x_6015_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5856_);
v___x_6018_ = l_Bool_repr___redArg(v_ground_5840_);
v___x_6019_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_5970_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set_uint8(v___x_6020_, sizeof(void*)*1, v___x_5862_);
v___x_6021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6017_);
lean_ctor_set(v___x_6021_, 1, v___x_6020_);
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
lean_ctor_set(v___x_6022_, 1, v___x_5865_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_5867_);
v___x_6024_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6023_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_5856_);
v___x_6027_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6028_ = l_Bool_repr___redArg(v_unfoldPartialApp_5841_);
v___x_6029_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6027_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
lean_ctor_set_uint8(v___x_6030_, sizeof(void*)*1, v___x_5862_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6026_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_5865_);
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set(v___x_6033_, 1, v___x_5867_);
v___x_6034_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6033_);
lean_ctor_set(v___x_6035_, 1, v___x_6034_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
lean_ctor_set(v___x_6036_, 1, v___x_5856_);
v___x_6037_ = l_Bool_repr___redArg(v_zetaDelta_5842_);
v___x_6038_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_5942_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6039_, 0, v___x_6038_);
lean_ctor_set_uint8(v___x_6039_, sizeof(void*)*1, v___x_5862_);
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6036_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_5865_);
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set(v___x_6042_, 1, v___x_5867_);
v___x_6043_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6042_);
lean_ctor_set(v___x_6044_, 1, v___x_6043_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set(v___x_6045_, 1, v___x_5856_);
v___x_6046_ = l_Bool_repr___redArg(v_index_5843_);
v___x_6047_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_5980_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set_uint8(v___x_6048_, sizeof(void*)*1, v___x_5862_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6045_);
lean_ctor_set(v___x_6049_, 1, v___x_6048_);
v___x_6050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
lean_ctor_set(v___x_6050_, 1, v___x_5865_);
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set(v___x_6051_, 1, v___x_5867_);
v___x_6052_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6051_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5856_);
v___x_6055_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6056_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5844_);
v___x_6057_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6055_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
lean_ctor_set_uint8(v___x_6058_, sizeof(void*)*1, v___x_5862_);
v___x_6059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6054_);
lean_ctor_set(v___x_6059_, 1, v___x_6058_);
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
lean_ctor_set(v___x_6060_, 1, v___x_5865_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set(v___x_6061_, 1, v___x_5867_);
v___x_6062_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6061_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set(v___x_6064_, 1, v___x_5856_);
v___x_6065_ = l_Bool_repr___redArg(v_zetaUnused_5845_);
v___x_6066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_5883_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set_uint8(v___x_6067_, sizeof(void*)*1, v___x_5862_);
v___x_6068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6064_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set(v___x_6069_, 1, v___x_5865_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set(v___x_6070_, 1, v___x_5867_);
v___x_6071_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6070_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_5856_);
v___x_6074_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6075_ = l_Bool_repr___redArg(v_catchRuntime_5846_);
v___x_6076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6074_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6077_, 0, v___x_6076_);
lean_ctor_set_uint8(v___x_6077_, sizeof(void*)*1, v___x_5862_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6073_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set(v___x_6079_, 1, v___x_5865_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
lean_ctor_set(v___x_6080_, 1, v___x_5867_);
v___x_6081_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6080_);
lean_ctor_set(v___x_6082_, 1, v___x_6081_);
v___x_6083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set(v___x_6083_, 1, v___x_5856_);
v___x_6084_ = l_Bool_repr___redArg(v_zetaHave_5847_);
v___x_6085_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_5858_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
lean_ctor_set_uint8(v___x_6086_, sizeof(void*)*1, v___x_5862_);
v___x_6087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6083_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set(v___x_6088_, 1, v___x_5865_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set(v___x_6089_, 1, v___x_5867_);
v___x_6090_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6089_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
lean_ctor_set(v___x_6092_, 1, v___x_5856_);
v___x_6093_ = l_Bool_repr___redArg(v_letToHave_5848_);
v___x_6094_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_5942_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set_uint8(v___x_6095_, sizeof(void*)*1, v___x_5862_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6092_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6096_);
lean_ctor_set(v___x_6097_, 1, v___x_5865_);
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set(v___x_6098_, 1, v___x_5867_);
v___x_6099_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6098_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5856_);
v___x_6102_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6103_ = l_Bool_repr___redArg(v_congrConsts_5849_);
v___x_6104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6102_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set_uint8(v___x_6105_, sizeof(void*)*1, v___x_5862_);
v___x_6106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6101_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
v___x_6107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set(v___x_6107_, 1, v___x_5865_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v___x_5867_);
v___x_6109_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6108_);
lean_ctor_set(v___x_6110_, 1, v___x_6109_);
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set(v___x_6111_, 1, v___x_5856_);
v___x_6112_ = l_Bool_repr___redArg(v_bitVecOfNat_5850_);
v___x_6113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6102_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set_uint8(v___x_6114_, sizeof(void*)*1, v___x_5862_);
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6111_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v___x_5865_);
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_5867_);
v___x_6118_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6117_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_5856_);
v___x_6121_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6122_ = l_Bool_repr___redArg(v_warnExponents_5851_);
v___x_6123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6121_);
lean_ctor_set(v___x_6123_, 1, v___x_6122_);
v___x_6124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set_uint8(v___x_6124_, sizeof(void*)*1, v___x_5862_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6120_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set(v___x_6126_, 1, v___x_5865_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
lean_ctor_set(v___x_6127_, 1, v___x_5867_);
v___x_6128_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6127_);
lean_ctor_set(v___x_6129_, 1, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
lean_ctor_set(v___x_6130_, 1, v___x_5856_);
v___x_6131_ = l_Bool_repr___redArg(v_suggestions_5852_);
v___x_6132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6102_);
lean_ctor_set(v___x_6132_, 1, v___x_6131_);
v___x_6133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set_uint8(v___x_6133_, sizeof(void*)*1, v___x_5862_);
v___x_6134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6130_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set(v___x_6135_, 1, v___x_5865_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set(v___x_6136_, 1, v___x_5867_);
v___x_6137_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6136_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set(v___x_6139_, 1, v___x_5856_);
v___x_6140_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6141_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5853_, v___x_5884_);
v___x_6142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6140_);
lean_ctor_set(v___x_6142_, 1, v___x_6141_);
v___x_6143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set_uint8(v___x_6143_, sizeof(void*)*1, v___x_5862_);
v___x_6144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6139_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set(v___x_6145_, 1, v___x_5865_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
lean_ctor_set(v___x_6146_, 1, v___x_5867_);
v___x_6147_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6146_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
v___x_6149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set(v___x_6149_, 1, v___x_5856_);
v___x_6150_ = l_Bool_repr___redArg(v_locals_5854_);
v___x_6151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_5970_);
lean_ctor_set(v___x_6151_, 1, v___x_6150_);
v___x_6152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
lean_ctor_set_uint8(v___x_6152_, sizeof(void*)*1, v___x_5862_);
v___x_6153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6149_);
lean_ctor_set(v___x_6153_, 1, v___x_6152_);
v___x_6154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6153_);
lean_ctor_set(v___x_6154_, 1, v___x_5865_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set(v___x_6155_, 1, v___x_5867_);
v___x_6156_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6155_);
lean_ctor_set(v___x_6157_, 1, v___x_6156_);
v___x_6158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
lean_ctor_set(v___x_6158_, 1, v___x_5856_);
v___x_6159_ = l_Bool_repr___redArg(v_instances_5855_);
v___x_6160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_5942_);
lean_ctor_set(v___x_6160_, 1, v___x_6159_);
v___x_6161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
lean_ctor_set_uint8(v___x_6161_, sizeof(void*)*1, v___x_5862_);
v___x_6162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6158_);
lean_ctor_set(v___x_6162_, 1, v___x_6161_);
v___x_6163_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6164_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6164_);
lean_ctor_set(v___x_6165_, 1, v___x_6162_);
v___x_6166_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6165_);
lean_ctor_set(v___x_6167_, 1, v___x_6166_);
v___x_6168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6163_);
lean_ctor_set(v___x_6168_, 1, v___x_6167_);
v___x_6169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
lean_ctor_set_uint8(v___x_6169_, sizeof(void*)*1, v___x_5862_);
return v___x_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6170_, lean_object* v_prec_6171_){
_start:
{
lean_object* v___x_6172_; 
v___x_6172_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6170_);
return v___x_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6173_, lean_object* v_prec_6174_){
_start:
{
lean_object* v_res_6175_; 
v_res_6175_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6173_, v_prec_6174_);
lean_dec(v_prec_6174_);
return v_res_6175_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6178_, lean_object* v_x_6179_){
_start:
{
if (lean_obj_tag(v_x_6179_) == 0)
{
uint8_t v___x_6180_; 
v___x_6180_ = 0;
return v___x_6180_;
}
else
{
lean_object* v_head_6181_; lean_object* v_tail_6182_; uint8_t v___x_6183_; 
v_head_6181_ = lean_ctor_get(v_x_6179_, 0);
v_tail_6182_ = lean_ctor_get(v_x_6179_, 1);
v___x_6183_ = lean_nat_dec_eq(v_a_6178_, v_head_6181_);
if (v___x_6183_ == 0)
{
v_x_6179_ = v_tail_6182_;
goto _start;
}
else
{
return v___x_6183_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6185_, lean_object* v_x_6186_){
_start:
{
uint8_t v_res_6187_; lean_object* v_r_6188_; 
v_res_6187_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6185_, v_x_6186_);
lean_dec(v_x_6186_);
lean_dec(v_a_6185_);
v_r_6188_ = lean_box(v_res_6187_);
return v_r_6188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6189_, lean_object* v_x_6190_){
_start:
{
switch(lean_obj_tag(v_x_6189_))
{
case 0:
{
uint8_t v___x_6191_; 
v___x_6191_ = 1;
return v___x_6191_;
}
case 1:
{
lean_object* v_idxs_6192_; uint8_t v___x_6193_; 
v_idxs_6192_ = lean_ctor_get(v_x_6189_, 0);
v___x_6193_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6190_, v_idxs_6192_);
return v___x_6193_;
}
default: 
{
lean_object* v_idxs_6194_; uint8_t v___x_6195_; 
v_idxs_6194_ = lean_ctor_get(v_x_6189_, 0);
v___x_6195_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6190_, v_idxs_6194_);
if (v___x_6195_ == 0)
{
uint8_t v___x_6196_; 
v___x_6196_ = 1;
return v___x_6196_;
}
else
{
uint8_t v___x_6197_; 
v___x_6197_ = 0;
return v___x_6197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6198_, lean_object* v_x_6199_){
_start:
{
uint8_t v_res_6200_; lean_object* v_r_6201_; 
v_res_6200_ = l_Lean_Meta_Occurrences_contains(v_x_6198_, v_x_6199_);
lean_dec(v_x_6199_);
lean_dec(v_x_6198_);
v_r_6201_ = lean_box(v_res_6200_);
return v_r_6201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6202_){
_start:
{
if (lean_obj_tag(v_x_6202_) == 0)
{
uint8_t v___x_6203_; 
v___x_6203_ = 1;
return v___x_6203_;
}
else
{
uint8_t v___x_6204_; 
v___x_6204_ = 0;
return v___x_6204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6205_){
_start:
{
uint8_t v_res_6206_; lean_object* v_r_6207_; 
v_res_6206_ = l_Lean_Meta_Occurrences_isAll(v_x_6205_);
lean_dec(v_x_6205_);
v_r_6207_ = lean_box(v_res_6206_);
return v_r_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6208_){
_start:
{
switch(v_x_6208_)
{
case 0:
{
lean_object* v___x_6209_; 
v___x_6209_ = lean_unsigned_to_nat(0u);
return v___x_6209_;
}
case 1:
{
lean_object* v___x_6210_; 
v___x_6210_ = lean_unsigned_to_nat(1u);
return v___x_6210_;
}
default: 
{
lean_object* v___x_6211_; 
v___x_6211_ = lean_unsigned_to_nat(2u);
return v___x_6211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6212_){
_start:
{
uint8_t v_x_boxed_6213_; lean_object* v_res_6214_; 
v_x_boxed_6213_ = lean_unbox(v_x_6212_);
v_res_6214_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6213_);
return v_res_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6215_){
_start:
{
lean_inc(v_k_6215_);
return v_k_6215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6216_){
_start:
{
lean_object* v_res_6217_; 
v_res_6217_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6216_);
lean_dec(v_k_6216_);
return v_res_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6218_, lean_object* v_ctorIdx_6219_, uint8_t v_t_6220_, lean_object* v_h_6221_, lean_object* v_k_6222_){
_start:
{
lean_inc(v_k_6222_);
return v_k_6222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6223_, lean_object* v_ctorIdx_6224_, lean_object* v_t_6225_, lean_object* v_h_6226_, lean_object* v_k_6227_){
_start:
{
uint8_t v_t_boxed_6228_; lean_object* v_res_6229_; 
v_t_boxed_6228_ = lean_unbox(v_t_6225_);
v_res_6229_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6223_, v_ctorIdx_6224_, v_t_boxed_6228_, v_h_6226_, v_k_6227_);
lean_dec(v_k_6227_);
lean_dec(v_ctorIdx_6224_);
return v_res_6229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6230_){
_start:
{
lean_inc(v_nonDependentFirst_6230_);
return v_nonDependentFirst_6230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6231_){
_start:
{
lean_object* v_res_6232_; 
v_res_6232_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6231_);
lean_dec(v_nonDependentFirst_6231_);
return v_res_6232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6233_, uint8_t v_t_6234_, lean_object* v_h_6235_, lean_object* v_nonDependentFirst_6236_){
_start:
{
lean_inc(v_nonDependentFirst_6236_);
return v_nonDependentFirst_6236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6237_, lean_object* v_t_6238_, lean_object* v_h_6239_, lean_object* v_nonDependentFirst_6240_){
_start:
{
uint8_t v_t_boxed_6241_; lean_object* v_res_6242_; 
v_t_boxed_6241_ = lean_unbox(v_t_6238_);
v_res_6242_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6237_, v_t_boxed_6241_, v_h_6239_, v_nonDependentFirst_6240_);
lean_dec(v_nonDependentFirst_6240_);
return v_res_6242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6243_){
_start:
{
lean_inc(v_nonDependentOnly_6243_);
return v_nonDependentOnly_6243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6244_){
_start:
{
lean_object* v_res_6245_; 
v_res_6245_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6244_);
lean_dec(v_nonDependentOnly_6244_);
return v_res_6245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6246_, uint8_t v_t_6247_, lean_object* v_h_6248_, lean_object* v_nonDependentOnly_6249_){
_start:
{
lean_inc(v_nonDependentOnly_6249_);
return v_nonDependentOnly_6249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6250_, lean_object* v_t_6251_, lean_object* v_h_6252_, lean_object* v_nonDependentOnly_6253_){
_start:
{
uint8_t v_t_boxed_6254_; lean_object* v_res_6255_; 
v_t_boxed_6254_ = lean_unbox(v_t_6251_);
v_res_6255_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6250_, v_t_boxed_6254_, v_h_6252_, v_nonDependentOnly_6253_);
lean_dec(v_nonDependentOnly_6253_);
return v_res_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6256_){
_start:
{
lean_inc(v_all_6256_);
return v_all_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6257_){
_start:
{
lean_object* v_res_6258_; 
v_res_6258_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6257_);
lean_dec(v_all_6257_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6259_, uint8_t v_t_6260_, lean_object* v_h_6261_, lean_object* v_all_6262_){
_start:
{
lean_inc(v_all_6262_);
return v_all_6262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6263_, lean_object* v_t_6264_, lean_object* v_h_6265_, lean_object* v_all_6266_){
_start:
{
uint8_t v_t_boxed_6267_; lean_object* v_res_6268_; 
v_t_boxed_6267_ = lean_unbox(v_t_6264_);
v_res_6268_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6263_, v_t_boxed_6267_, v_h_6265_, v_all_6266_);
lean_dec(v_all_6266_);
return v_res_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6282_){
_start:
{
lean_object* v___x_6283_; uint8_t v___x_6284_; 
v___x_6283_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6282_);
v___x_6284_ = l_Lean_Syntax_isOfKind(v_c_6282_, v___x_6283_);
if (v___x_6284_ == 0)
{
lean_object* v___x_6285_; uint8_t v___x_6286_; 
v___x_6285_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6282_);
v___x_6286_ = l_Lean_Syntax_isOfKind(v_c_6282_, v___x_6285_);
if (v___x_6286_ == 0)
{
lean_object* v___x_6287_; uint8_t v___x_6288_; 
v___x_6287_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6282_);
v___x_6288_ = l_Lean_Syntax_isOfKind(v_c_6282_, v___x_6287_);
if (v___x_6288_ == 0)
{
lean_object* v___x_6289_; 
lean_dec(v_c_6282_);
v___x_6289_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6289_;
}
else
{
lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; 
v___x_6290_ = lean_unsigned_to_nat(1u);
v___x_6291_ = lean_mk_empty_array_with_capacity(v___x_6290_);
v___x_6292_ = lean_array_push(v___x_6291_, v_c_6282_);
return v___x_6292_;
}
}
else
{
lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; 
v___x_6293_ = lean_unsigned_to_nat(0u);
v___x_6294_ = l_Lean_Syntax_getArg(v_c_6282_, v___x_6293_);
lean_dec(v_c_6282_);
v___x_6295_ = l_Lean_Syntax_getArgs(v___x_6294_);
lean_dec(v___x_6294_);
return v___x_6295_;
}
}
else
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; uint8_t v___x_6300_; 
v___x_6296_ = l_Lean_Syntax_getArgs(v_c_6282_);
lean_dec(v_c_6282_);
v___x_6297_ = lean_unsigned_to_nat(0u);
v___x_6298_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6299_ = lean_array_get_size(v___x_6296_);
v___x_6300_ = lean_nat_dec_lt(v___x_6297_, v___x_6299_);
if (v___x_6300_ == 0)
{
lean_dec_ref(v___x_6296_);
return v___x_6298_;
}
else
{
size_t v___x_6301_; size_t v___x_6302_; lean_object* v___x_6303_; 
v___x_6301_ = ((size_t)0ULL);
v___x_6302_ = lean_usize_of_nat(v___x_6299_);
v___x_6303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6296_, v___x_6301_, v___x_6302_, v___x_6298_);
lean_dec_ref(v___x_6296_);
return v___x_6303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6304_, size_t v_i_6305_, size_t v_stop_6306_, lean_object* v_b_6307_){
_start:
{
uint8_t v___x_6308_; 
v___x_6308_ = lean_usize_dec_eq(v_i_6305_, v_stop_6306_);
if (v___x_6308_ == 0)
{
lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; size_t v___x_6312_; size_t v___x_6313_; 
v___x_6309_ = lean_array_uget_borrowed(v_as_6304_, v_i_6305_);
lean_inc(v___x_6309_);
v___x_6310_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6309_);
v___x_6311_ = l_Array_append___redArg(v_b_6307_, v___x_6310_);
lean_dec_ref(v___x_6310_);
v___x_6312_ = ((size_t)1ULL);
v___x_6313_ = lean_usize_add(v_i_6305_, v___x_6312_);
v_i_6305_ = v___x_6313_;
v_b_6307_ = v___x_6311_;
goto _start;
}
else
{
return v_b_6307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6315_, lean_object* v_i_6316_, lean_object* v_stop_6317_, lean_object* v_b_6318_){
_start:
{
size_t v_i_boxed_6319_; size_t v_stop_boxed_6320_; lean_object* v_res_6321_; 
v_i_boxed_6319_ = lean_unbox_usize(v_i_6316_);
lean_dec(v_i_6316_);
v_stop_boxed_6320_ = lean_unbox_usize(v_stop_6317_);
lean_dec(v_stop_6317_);
v_res_6321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6315_, v_i_boxed_6319_, v_stop_boxed_6320_, v_b_6318_);
lean_dec_ref(v_as_6315_);
return v_res_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6322_){
_start:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6323_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6324_ = lean_box(2);
v___x_6325_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6326_, 0, v___x_6324_);
lean_ctor_set(v___x_6326_, 1, v___x_6325_);
lean_ctor_set(v___x_6326_, 2, v_items_6322_);
v___x_6327_ = l_Lean_Syntax_node1(v___x_6324_, v___x_6323_, v___x_6326_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6328_, lean_object* v_cfg_x27_6329_){
_start:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; 
v___x_6330_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6328_);
v___x_6331_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6329_);
v___x_6332_ = l_Array_append___redArg(v___x_6330_, v___x_6331_);
lean_dec_ref(v___x_6331_);
v___x_6333_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6332_);
return v___x_6333_;
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
