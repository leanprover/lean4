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
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
static const lean_closure_object l_Lean_Syntax_instBEqTSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqTSyntax___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqTSyntax___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_400_){
_start:
{
switch(lean_obj_tag(v_x_400_))
{
case 1:
{
lean_object* v_str_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v_str_401_ = lean_ctor_get(v_x_400_, 1);
lean_inc_ref_n(v_str_401_, 2);
lean_dec_ref_known(v_x_400_, 2);
v___x_402_ = 10013;
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
lean_dec_ref_known(v_x_400_, 2);
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
v_res_410_ = l_Lean_Name_isInaccessibleUserName(v_x_409_);
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
lean_inc_ref_n(v_str_820_, 2);
lean_dec_ref_known(v_n_816_, 2);
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
lean_inc_ref_n(v_str_824_, 2);
lean_dec_ref_known(v_n_816_, 2);
lean_inc_ref(v_isToken_817_);
v_r_825_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_814_, v_escape_815_, v_pre_819_, v_isToken_817_);
v___x_826_ = lean_string_append(v_r_825_, v_sep_814_);
v___x_827_ = 0;
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
lean_dec_ref_known(v_n_816_, 2);
v___x_836_ = l_Nat_reprFast(v_i_835_);
return v___x_836_;
}
else
{
lean_object* v_i_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc(v_pre_834_);
v_i_837_ = lean_ctor_get(v_n_816_, 1);
lean_inc(v_i_837_);
lean_dec_ref_known(v_n_816_, 2);
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
lean_inc_ref_n(v_str_859_, 2);
lean_dec_ref_known(v___x_858_, 2);
v___x_860_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
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
v___x_872_ = l_Lean_Name_isInaccessibleUserName(v_n_867_);
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
lean_dec_ref_known(v_n_887_, 2);
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
lean_dec_ref_known(v_n_887_, 2);
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
lean_dec_ref_known(v_n_887_, 2);
v___x_901_ = l_Nat_reprFast(v_i_900_);
return v___x_901_;
}
else
{
lean_object* v_i_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v_pre_899_);
v_i_902_ = lean_ctor_get(v_n_887_, 1);
lean_inc(v_i_902_);
lean_dec_ref_known(v_n_887_, 2);
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
v___x_916_ = l_Lean_Name_isInaccessibleUserName(v_n_912_);
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
lean_dec_ref_known(v_n_958_, 2);
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
lean_dec_ref_known(v_n_958_, 2);
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
lean_dec_ref_known(v_x_996_, 2);
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
lean_dec_ref_known(v_x_1001_, 2);
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
lean_dec_ref_known(v_x_1001_, 2);
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
lean_dec_ref_known(v_x_1018_, 2);
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
lean_dec_ref_known(v_x_1018_, 2);
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
lean_dec_ref_known(v_x_1059_, 2);
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
lean_dec_ref_known(v_x_1084_, 2);
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
lean_dec_ref_known(v_x_1115_, 2);
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
lean_dec_ref_known(v_x_1115_, 2);
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
lean_dec_ref_known(v_x_1143_, 2);
v_pre_1154_ = lean_ctor_get(v_x_1144_, 0);
lean_inc(v_pre_1154_);
v_str_1155_ = lean_ctor_get(v_x_1144_, 1);
lean_inc_ref(v_str_1155_);
lean_dec_ref_known(v_x_1144_, 2);
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
lean_dec_ref_known(v_x_1143_, 2);
v_pre_1160_ = lean_ctor_get(v_x_1144_, 0);
lean_inc(v_pre_1160_);
v_i_1161_ = lean_ctor_get(v_x_1144_, 1);
lean_inc(v_i_1161_);
lean_dec_ref_known(v_x_1144_, 2);
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
lean_dec_ref_known(v_x_1165_, 2);
v_pre_1176_ = lean_ctor_get(v_x_1166_, 0);
lean_inc(v_pre_1176_);
v_str_1177_ = lean_ctor_get(v_x_1166_, 1);
lean_inc_ref(v_str_1177_);
lean_dec_ref_known(v_x_1166_, 2);
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
lean_dec_ref_known(v_x_1165_, 2);
v_pre_1182_ = lean_ctor_get(v_x_1166_, 0);
lean_inc(v_pre_1182_);
v_i_1183_ = lean_ctor_get(v_x_1166_, 1);
lean_inc(v_i_1183_);
lean_dec_ref_known(v_x_1166_, 2);
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
lean_inc_n(v_toBind_1250_, 2);
lean_dec_ref(v_inst_1247_);
v_getNGen_1251_ = lean_ctor_get(v_inst_1248_, 0);
lean_inc(v_getNGen_1251_);
v_setNGen_1252_ = lean_ctor_get(v_inst_1248_, 1);
lean_inc(v_setNGen_1252_);
lean_dec_ref(v_inst_1248_);
v_toPure_1253_ = lean_ctor_get(v_toApplicative_1249_, 1);
lean_inc(v_toPure_1253_);
lean_dec_ref(v_toApplicative_1249_);
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
lean_dec_ref_known(v_x_1318_, 2);
v___x_1323_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1322_);
return v___x_1323_;
}
else
{
lean_object* v_head_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_inc(v_tail_1321_);
v_head_1324_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_head_1324_);
lean_dec_ref_known(v_x_1318_, 2);
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
lean_dec_ref_known(v_x_1373_, 1);
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
lean_inc(v___y_1377_);
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
lean_inc(v___y_1396_);
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
lean_dec_ref_known(v_x_1464_, 2);
v___x_1469_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1468_);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v_tail_1467_);
v_head_1470_ = lean_ctor_get(v_x_1464_, 0);
lean_inc(v_head_1470_);
lean_dec_ref_known(v_x_1464_, 2);
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
lean_dec_ref_known(v_x_1526_, 2);
v___x_1531_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1530_);
return v___x_1531_;
}
else
{
lean_object* v_head_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_inc(v_tail_1529_);
v_head_1532_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_head_1532_);
lean_dec_ref_known(v_x_1526_, 2);
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
lean_dec_ref_known(v_x_1573_, 3);
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
lean_inc(v___y_1590_);
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
lean_inc(v___y_1616_);
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
lean_dec_ref_known(v_x_1573_, 4);
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
lean_inc(v___y_1642_);
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
lean_inc(v___y_1576_);
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
v_args_1827_ = lean_ctor_get(v_x_1822_, 2);
v_kind_1828_ = lean_ctor_get(v_x_1823_, 1);
v_args_1829_ = lean_ctor_get(v_x_1823_, 2);
v___x_1830_ = lean_name_eq(v_kind_1826_, v_kind_1828_);
if (v___x_1830_ == 0)
{
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
return v___x_1833_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1827_, v_args_1829_, v___x_1831_);
return v___x_1834_;
}
}
}
else
{
uint8_t v___x_1835_; 
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
v_val_1837_ = lean_ctor_get(v_x_1823_, 1);
v___x_1838_ = lean_string_dec_eq(v_val_1836_, v_val_1837_);
return v___x_1838_;
}
else
{
uint8_t v___x_1839_; 
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
v_val_1841_ = lean_ctor_get(v_x_1822_, 2);
v_preresolved_1842_ = lean_ctor_get(v_x_1822_, 3);
v_rawVal_1843_ = lean_ctor_get(v_x_1823_, 1);
v_val_1844_ = lean_ctor_get(v_x_1823_, 2);
v_preresolved_1845_ = lean_ctor_get(v_x_1823_, 3);
lean_inc_ref(v_rawVal_1843_);
lean_inc_ref(v_rawVal_1840_);
v___x_1849_ = lean_substring_beq(v_rawVal_1840_, v_rawVal_1843_);
if (v___x_1849_ == 0)
{
v___y_1847_ = v___x_1849_;
goto v___jp_1846_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_name_eq(v_val_1841_, v_val_1844_);
v___y_1847_ = v___x_1850_;
goto v___jp_1846_;
}
v___jp_1846_:
{
if (v___y_1847_ == 0)
{
return v___y_1847_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1842_, v_preresolved_1845_);
return v___x_1848_;
}
}
}
else
{
uint8_t v___x_1851_; 
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
lean_dec(v_x_1869_);
lean_dec(v_x_1868_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1888_){
_start:
{
lean_object* v___f_1889_; 
v___f_1889_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___closed__0));
return v___f_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Syntax_instBEqTSyntax(v_k_1890_);
lean_dec(v_k_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1892_, lean_object* v_i_1893_){
_start:
{
lean_object* v_zero_1894_; uint8_t v_isZero_1895_; 
v_zero_1894_ = lean_unsigned_to_nat(0u);
v_isZero_1895_ = lean_nat_dec_eq(v_i_1893_, v_zero_1894_);
if (v_isZero_1895_ == 1)
{
lean_object* v___x_1896_; 
lean_dec(v_i_1893_);
v___x_1896_ = lean_box(0);
return v___x_1896_;
}
else
{
lean_object* v_one_1897_; lean_object* v_n_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_one_1897_ = lean_unsigned_to_nat(1u);
v_n_1898_ = lean_nat_sub(v_i_1893_, v_one_1897_);
lean_dec(v_i_1893_);
v___x_1899_ = lean_array_fget_borrowed(v_as_1892_, v_n_1898_);
v___x_1900_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1899_);
if (lean_obj_tag(v___x_1900_) == 0)
{
v_i_1893_ = v_n_1898_;
goto _start;
}
else
{
lean_dec(v_n_1898_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1902_){
_start:
{
switch(lean_obj_tag(v_x_1902_))
{
case 2:
{
lean_object* v_info_1903_; lean_object* v___x_1904_; 
v_info_1903_ = lean_ctor_get(v_x_1902_, 0);
lean_inc(v_info_1903_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_info_1903_);
return v___x_1904_;
}
case 3:
{
lean_object* v_info_1905_; lean_object* v___x_1906_; 
v_info_1905_ = lean_ctor_get(v_x_1902_, 0);
lean_inc(v_info_1905_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_info_1905_);
return v___x_1906_;
}
case 1:
{
lean_object* v_info_1907_; 
v_info_1907_ = lean_ctor_get(v_x_1902_, 0);
if (lean_obj_tag(v_info_1907_) == 2)
{
lean_object* v_args_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_args_1908_ = lean_ctor_get(v_x_1902_, 2);
v___x_1909_ = lean_array_get_size(v_args_1908_);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1908_, v___x_1909_);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; 
lean_inc(v_info_1907_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_info_1907_);
return v___x_1911_;
}
}
default: 
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1913_);
lean_dec(v_x_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1915_, lean_object* v_i_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1915_, v_i_1916_);
lean_dec_ref(v_as_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1918_, lean_object* v_i_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1918_, v_i_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1922_, lean_object* v_i_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1922_, v_i_1923_, v_a_1924_);
lean_dec_ref(v_as_1922_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_box(2);
return v___x_1928_;
}
else
{
lean_object* v_val_1929_; 
v_val_1929_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v___x_1927_, 1);
return v_val_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Syntax_getTailInfo(v_stx_1930_);
lean_dec(v_stx_1930_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1932_);
if (lean_obj_tag(v___x_1933_) == 1)
{
lean_object* v_val_1934_; 
v_val_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v___x_1933_, 1);
if (lean_obj_tag(v_val_1934_) == 0)
{
lean_object* v_trailing_1935_; lean_object* v_startPos_1936_; lean_object* v_stopPos_1937_; lean_object* v___x_1938_; 
v_trailing_1935_ = lean_ctor_get(v_val_1934_, 2);
lean_inc_ref(v_trailing_1935_);
lean_dec_ref_known(v_val_1934_, 4);
v_startPos_1936_ = lean_ctor_get(v_trailing_1935_, 1);
lean_inc(v_startPos_1936_);
v_stopPos_1937_ = lean_ctor_get(v_trailing_1935_, 2);
lean_inc(v_stopPos_1937_);
lean_dec_ref(v_trailing_1935_);
v___x_1938_ = lean_nat_sub(v_stopPos_1937_, v_startPos_1936_);
lean_dec(v_startPos_1936_);
lean_dec(v_stopPos_1937_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; 
lean_dec(v_val_1934_);
v___x_1939_ = lean_unsigned_to_nat(0u);
return v___x_1939_;
}
}
else
{
lean_object* v___x_1940_; 
lean_dec(v___x_1933_);
v___x_1940_ = lean_unsigned_to_nat(0u);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Syntax_getTrailingSize(v_stx_1941_);
lean_dec(v_stx_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = l_Lean_Syntax_getTailInfo(v_stx_1943_);
v___x_1945_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1944_);
lean_dec(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1946_);
lean_dec(v_stx_1946_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1948_, uint8_t v_canonicalOnly_1949_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = l_Lean_Syntax_getTailInfo(v_stx_1948_);
v___x_1951_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1950_, v_canonicalOnly_1949_);
lean_dec(v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1952_, lean_object* v_canonicalOnly_1953_){
_start:
{
uint8_t v_canonicalOnly_boxed_1954_; lean_object* v_res_1955_; 
v_canonicalOnly_boxed_1954_ = lean_unbox(v_canonicalOnly_1953_);
v_res_1955_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1952_, v_canonicalOnly_boxed_1954_);
lean_dec(v_stx_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1956_, uint8_t v_withLeading_1957_, uint8_t v_withTrailing_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_Syntax_getHeadInfo(v_stx_1956_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_leading_1960_; lean_object* v_pos_1961_; lean_object* v___x_1962_; 
v_leading_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_ref(v_leading_1960_);
v_pos_1961_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_pos_1961_);
lean_dec_ref_known(v___x_1959_, 4);
v___x_1962_ = l_Lean_Syntax_getTailInfo(v_stx_1956_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_trailing_1963_; lean_object* v_endPos_1964_; lean_object* v_str_1965_; lean_object* v_startPos_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1980_; 
v_trailing_1963_ = lean_ctor_get(v___x_1962_, 2);
lean_inc_ref(v_trailing_1963_);
v_endPos_1964_ = lean_ctor_get(v___x_1962_, 3);
lean_inc(v_endPos_1964_);
lean_dec_ref_known(v___x_1962_, 4);
v_str_1965_ = lean_ctor_get(v_leading_1960_, 0);
v_startPos_1966_ = lean_ctor_get(v_leading_1960_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_leading_1960_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v_leading_1960_, 2);
lean_dec(v_unused_1981_);
v___x_1968_ = v_leading_1960_;
v_isShared_1969_ = v_isSharedCheck_1980_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_startPos_1966_);
lean_inc(v_str_1965_);
lean_dec(v_leading_1960_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1980_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1978_; 
if (v_withLeading_1957_ == 0)
{
lean_dec(v_startPos_1966_);
v___y_1978_ = v_pos_1961_;
goto v___jp_1977_;
}
else
{
lean_dec(v_pos_1961_);
v___y_1978_ = v_startPos_1966_;
goto v___jp_1977_;
}
v___jp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 2, v___y_1972_);
lean_ctor_set(v___x_1968_, 1, v___y_1971_);
v___x_1974_ = v___x_1968_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_str_1965_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___y_1971_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v___y_1972_);
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
v___jp_1977_:
{
if (v_withTrailing_1958_ == 0)
{
lean_dec_ref(v_trailing_1963_);
v___y_1971_ = v___y_1978_;
v___y_1972_ = v_endPos_1964_;
goto v___jp_1970_;
}
else
{
lean_object* v_stopPos_1979_; 
lean_dec(v_endPos_1964_);
v_stopPos_1979_ = lean_ctor_get(v_trailing_1963_, 2);
lean_inc(v_stopPos_1979_);
lean_dec_ref(v_trailing_1963_);
v___y_1971_ = v___y_1978_;
v___y_1972_ = v_stopPos_1979_;
goto v___jp_1970_;
}
}
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v___x_1962_);
lean_dec(v_pos_1961_);
lean_dec_ref(v_leading_1960_);
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1983_; 
lean_dec(v___x_1959_);
v___x_1983_ = lean_box(0);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1984_, lean_object* v_withLeading_1985_, lean_object* v_withTrailing_1986_){
_start:
{
uint8_t v_withLeading_boxed_1987_; uint8_t v_withTrailing_boxed_1988_; lean_object* v_res_1989_; 
v_withLeading_boxed_1987_ = lean_unbox(v_withLeading_1985_);
v_withTrailing_boxed_1988_ = lean_unbox(v_withTrailing_1986_);
v_res_1989_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1984_, v_withLeading_boxed_1987_, v_withTrailing_boxed_1988_);
lean_dec(v_stx_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1990_, lean_object* v_f_1991_, lean_object* v_i_1992_){
_start:
{
lean_object* v_zero_1993_; uint8_t v_isZero_1994_; 
v_zero_1993_ = lean_unsigned_to_nat(0u);
v_isZero_1994_ = lean_nat_dec_eq(v_i_1992_, v_zero_1993_);
if (v_isZero_1994_ == 1)
{
lean_object* v___x_1995_; 
lean_dec(v_i_1992_);
lean_dec_ref(v_f_1991_);
lean_dec_ref(v_a_1990_);
v___x_1995_ = lean_box(0);
return v___x_1995_;
}
else
{
lean_object* v_one_1996_; lean_object* v_n_1997_; lean_object* v_v_1998_; lean_object* v___x_1999_; 
v_one_1996_ = lean_unsigned_to_nat(1u);
v_n_1997_ = lean_nat_sub(v_i_1992_, v_one_1996_);
lean_dec(v_i_1992_);
v_v_1998_ = lean_array_fget_borrowed(v_a_1990_, v_n_1997_);
lean_inc_ref(v_f_1991_);
lean_inc(v_v_1998_);
v___x_1999_ = lean_apply_1(v_f_1991_, v_v_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
v_i_1992_ = v_n_1997_;
goto _start;
}
else
{
lean_object* v_val_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_f_1991_);
v_val_2001_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v___x_1999_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_val_2001_);
lean_dec(v___x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_array_fset(v_a_1990_, v_n_1997_, v_val_2001_);
lean_dec(v_n_1997_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_2010_, lean_object* v_a_2011_, lean_object* v_f_2012_, lean_object* v_i_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_2011_, v_f_2012_, v_i_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_2015_, lean_object* v_x_2016_){
_start:
{
switch(lean_obj_tag(v_x_2016_))
{
case 2:
{
lean_object* v_val_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
v_val_2017_ = lean_ctor_get(v_x_2016_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v_x_2016_, 0);
lean_dec(v_unused_2026_);
v___x_2019_ = v_x_2016_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_val_2017_);
lean_dec(v_x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_info_2015_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_info_2015_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_val_2017_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
case 3:
{
lean_object* v_rawVal_2027_; lean_object* v_val_2028_; lean_object* v_preresolved_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2037_; 
v_rawVal_2027_ = lean_ctor_get(v_x_2016_, 1);
v_val_2028_ = lean_ctor_get(v_x_2016_, 2);
v_preresolved_2029_ = lean_ctor_get(v_x_2016_, 3);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_x_2016_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v_x_2016_, 0);
lean_dec(v_unused_2038_);
v___x_2031_ = v_x_2016_;
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_preresolved_2029_);
lean_inc(v_val_2028_);
lean_inc(v_rawVal_2027_);
lean_dec(v_x_2016_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v_info_2015_);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_info_2015_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_rawVal_2027_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_val_2028_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_preresolved_2029_);
v___x_2034_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
}
}
case 1:
{
lean_object* v_info_2039_; lean_object* v_kind_2040_; lean_object* v_args_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2059_; 
v_info_2039_ = lean_ctor_get(v_x_2016_, 0);
v_kind_2040_ = lean_ctor_get(v_x_2016_, 1);
v_args_2041_ = lean_ctor_get(v_x_2016_, 2);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_x_2016_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2043_ = v_x_2016_;
v_isShared_2044_ = v_isSharedCheck_2059_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_args_2041_);
lean_inc(v_kind_2040_);
lean_inc(v_info_2039_);
lean_dec(v_x_2016_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2059_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_array_get_size(v_args_2041_);
v___x_2046_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_2015_, v_args_2041_, v___x_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; 
lean_del_object(v___x_2043_);
lean_dec(v_kind_2040_);
lean_dec(v_info_2039_);
v___x_2047_ = lean_box(0);
return v___x_2047_;
}
else
{
lean_object* v_val_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2058_; 
v_val_2048_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2050_ = v___x_2046_;
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_val_2048_);
lean_dec(v___x_2046_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v_val_2048_);
v___x_2053_ = v___x_2043_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_info_2039_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_kind_2040_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_val_2048_);
v___x_2053_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2053_);
v___x_2055_ = v___x_2050_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2060_; 
lean_dec(v_x_2016_);
lean_dec(v_info_2015_);
v___x_2060_ = lean_box(0);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2061_, lean_object* v_a_2062_, lean_object* v_i_2063_){
_start:
{
lean_object* v_zero_2064_; uint8_t v_isZero_2065_; 
v_zero_2064_ = lean_unsigned_to_nat(0u);
v_isZero_2065_ = lean_nat_dec_eq(v_i_2063_, v_zero_2064_);
if (v_isZero_2065_ == 1)
{
lean_object* v___x_2066_; 
lean_dec(v_i_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_info_2061_);
v___x_2066_ = lean_box(0);
return v___x_2066_;
}
else
{
lean_object* v_one_2067_; lean_object* v_n_2068_; lean_object* v_v_2069_; lean_object* v___x_2070_; 
v_one_2067_ = lean_unsigned_to_nat(1u);
v_n_2068_ = lean_nat_sub(v_i_2063_, v_one_2067_);
lean_dec(v_i_2063_);
v_v_2069_ = lean_array_fget_borrowed(v_a_2062_, v_n_2068_);
lean_inc(v_v_2069_);
lean_inc(v_info_2061_);
v___x_2070_ = l_Lean_Syntax_setTailInfoAux(v_info_2061_, v_v_2069_);
if (lean_obj_tag(v___x_2070_) == 0)
{
v_i_2063_ = v_n_2068_;
goto _start;
}
else
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_info_2061_);
v_val_2072_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2074_ = v___x_2070_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v___x_2070_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_array_fset(v_a_2062_, v_n_2068_, v_val_2072_);
lean_dec(v_n_2068_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2081_, lean_object* v_info_2082_){
_start:
{
lean_object* v___x_2083_; 
lean_inc(v_stx_2081_);
v___x_2083_ = l_Lean_Syntax_setTailInfoAux(v_info_2082_, v_stx_2081_);
if (lean_obj_tag(v___x_2083_) == 0)
{
return v_stx_2081_;
}
else
{
lean_object* v_val_2084_; 
lean_dec(v_stx_2081_);
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2083_, 1);
return v_val_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Syntax_getTailInfo(v_stx_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_trailing_2087_; lean_object* v_leading_2088_; lean_object* v_pos_2089_; lean_object* v_endPos_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2108_; 
v_trailing_2087_ = lean_ctor_get(v___x_2086_, 2);
v_leading_2088_ = lean_ctor_get(v___x_2086_, 0);
v_pos_2089_ = lean_ctor_get(v___x_2086_, 1);
v_endPos_2090_ = lean_ctor_get(v___x_2086_, 3);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2092_ = v___x_2086_;
v_isShared_2093_ = v_isSharedCheck_2108_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_endPos_2090_);
lean_inc(v_trailing_2087_);
lean_inc(v_pos_2089_);
lean_inc(v_leading_2088_);
lean_dec(v___x_2086_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2108_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_str_2094_; lean_object* v_startPos_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2106_; 
v_str_2094_ = lean_ctor_get(v_trailing_2087_, 0);
v_startPos_2095_ = lean_ctor_get(v_trailing_2087_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_trailing_2087_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v_trailing_2087_, 2);
lean_dec(v_unused_2107_);
v___x_2097_ = v_trailing_2087_;
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_startPos_2095_);
lean_inc(v_str_2094_);
lean_dec(v_trailing_2087_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
lean_inc(v_startPos_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 2, v_startPos_2095_);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_str_2094_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_startPos_2095_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_startPos_2095_);
v___x_2100_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 2, v___x_2100_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_leading_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_pos_2089_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v_endPos_2090_);
v___x_2102_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_Syntax_setTailInfo(v_stx_2085_, v___x_2102_);
return v___x_2103_;
}
}
}
}
}
else
{
lean_dec(v___x_2086_);
return v_stx_2085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2109_, lean_object* v_f_2110_, lean_object* v_i_2111_){
_start:
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = lean_array_get_size(v_a_2109_);
v___x_2113_ = lean_nat_dec_lt(v_i_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v_i_2111_);
lean_dec_ref(v_f_2110_);
lean_dec_ref(v_a_2109_);
v___x_2114_ = lean_box(0);
return v___x_2114_;
}
else
{
lean_object* v_v_2115_; lean_object* v___x_2116_; 
v_v_2115_ = lean_array_fget_borrowed(v_a_2109_, v_i_2111_);
lean_inc_ref(v_f_2110_);
lean_inc(v_v_2115_);
v___x_2116_ = lean_apply_1(v_f_2110_, v_v_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_unsigned_to_nat(1u);
v___x_2118_ = lean_nat_add(v_i_2111_, v___x_2117_);
lean_dec(v_i_2111_);
v_i_2111_ = v___x_2118_;
goto _start;
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_f_2110_);
v_val_2120_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2122_ = v___x_2116_;
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_val_2120_);
lean_dec(v___x_2116_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_array_fset(v_a_2109_, v_i_2111_, v_val_2120_);
lean_dec(v_i_2111_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2129_, lean_object* v_inst_2130_, lean_object* v_a_2131_, lean_object* v_f_2132_, lean_object* v_i_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2131_, v_f_2132_, v_i_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_inst_2136_, lean_object* v_a_2137_, lean_object* v_f_2138_, lean_object* v_i_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2135_, v_inst_2136_, v_a_2137_, v_f_2138_, v_i_2139_);
lean_dec(v_inst_2136_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2141_, lean_object* v_x_2142_){
_start:
{
switch(lean_obj_tag(v_x_2142_))
{
case 2:
{
lean_object* v_val_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2151_; 
v_val_2143_ = lean_ctor_get(v_x_2142_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2142_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_x_2142_, 0);
lean_dec(v_unused_2152_);
v___x_2145_ = v_x_2142_;
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_val_2143_);
lean_dec(v_x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v_info_2141_);
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_info_2141_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_val_2143_);
v___x_2148_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
}
}
case 3:
{
lean_object* v_rawVal_2153_; lean_object* v_val_2154_; lean_object* v_preresolved_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_rawVal_2153_ = lean_ctor_get(v_x_2142_, 1);
v_val_2154_ = lean_ctor_get(v_x_2142_, 2);
v_preresolved_2155_ = lean_ctor_get(v_x_2142_, 3);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_x_2142_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v_x_2142_, 0);
lean_dec(v_unused_2164_);
v___x_2157_ = v_x_2142_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_preresolved_2155_);
lean_inc(v_val_2154_);
lean_inc(v_rawVal_2153_);
lean_dec(v_x_2142_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v_info_2141_);
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_info_2141_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_rawVal_2153_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_val_2154_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_preresolved_2155_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
}
case 1:
{
lean_object* v_info_2165_; lean_object* v_kind_2166_; lean_object* v_args_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2185_; 
v_info_2165_ = lean_ctor_get(v_x_2142_, 0);
v_kind_2166_ = lean_ctor_get(v_x_2142_, 1);
v_args_2167_ = lean_ctor_get(v_x_2142_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_x_2142_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2169_ = v_x_2142_;
v_isShared_2170_ = v_isSharedCheck_2185_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_args_2167_);
lean_inc(v_kind_2166_);
lean_inc(v_info_2165_);
lean_dec(v_x_2142_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2185_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2141_, v_args_2167_, v___x_2171_);
if (lean_obj_tag(v___x_2172_) == 1)
{
lean_object* v_val_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2183_; 
v_val_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_val_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 2, v_val_2173_);
v___x_2178_ = v___x_2169_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_info_2165_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_kind_2166_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_val_2173_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v___x_2184_; 
lean_dec(v___x_2172_);
lean_del_object(v___x_2169_);
lean_dec(v_kind_2166_);
lean_dec(v_info_2165_);
v___x_2184_ = lean_box(0);
return v___x_2184_;
}
}
}
default: 
{
lean_object* v___x_2186_; 
lean_dec(v_x_2142_);
lean_dec(v_info_2141_);
v___x_2186_ = lean_box(0);
return v___x_2186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2187_, lean_object* v_a_2188_, lean_object* v_i_2189_){
_start:
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = lean_array_get_size(v_a_2188_);
v___x_2191_ = lean_nat_dec_lt(v_i_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_i_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_info_2187_);
v___x_2192_ = lean_box(0);
return v___x_2192_;
}
else
{
lean_object* v_v_2193_; lean_object* v___x_2194_; 
v_v_2193_ = lean_array_fget_borrowed(v_a_2188_, v_i_2189_);
lean_inc(v_v_2193_);
lean_inc(v_info_2187_);
v___x_2194_ = l_Lean_Syntax_setHeadInfoAux(v_info_2187_, v_v_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = lean_nat_add(v_i_2189_, v___x_2195_);
lean_dec(v_i_2189_);
v_i_2189_ = v___x_2196_;
goto _start;
}
else
{
lean_object* v_val_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_info_2187_);
v_val_2198_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2200_ = v___x_2194_;
v_isShared_2201_ = v_isSharedCheck_2206_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_val_2198_);
lean_dec(v___x_2194_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2206_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2202_ = lean_array_fset(v_a_2188_, v_i_2189_, v_val_2198_);
lean_dec(v_i_2189_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2202_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2207_, lean_object* v_info_2208_){
_start:
{
lean_object* v___x_2209_; 
lean_inc(v_stx_2207_);
v___x_2209_ = l_Lean_Syntax_setHeadInfoAux(v_info_2208_, v_stx_2207_);
if (lean_obj_tag(v___x_2209_) == 0)
{
return v_stx_2207_;
}
else
{
lean_object* v_val_2210_; 
lean_dec(v_stx_2207_);
v_val_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v___x_2209_, 1);
return v_val_2210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2211_, lean_object* v_x_2212_){
_start:
{
switch(lean_obj_tag(v_x_2212_))
{
case 0:
{
lean_dec(v_info_2211_);
return v_x_2212_;
}
case 1:
{
lean_object* v_kind_2213_; lean_object* v_args_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_kind_2213_ = lean_ctor_get(v_x_2212_, 1);
v_args_2214_ = lean_ctor_get(v_x_2212_, 2);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_x_2212_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v_x_2212_, 0);
lean_dec(v_unused_2222_);
v___x_2216_ = v_x_2212_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_args_2214_);
lean_inc(v_kind_2213_);
lean_dec(v_x_2212_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v_info_2211_);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_info_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_kind_2213_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_args_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
case 2:
{
lean_object* v_val_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_val_2223_ = lean_ctor_get(v_x_2212_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_x_2212_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_x_2212_, 0);
lean_dec(v_unused_2231_);
v___x_2225_ = v_x_2212_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_val_2223_);
lean_dec(v_x_2212_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_info_2211_);
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_info_2211_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_val_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
default: 
{
lean_object* v_rawVal_2232_; lean_object* v_val_2233_; lean_object* v_preresolved_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_rawVal_2232_ = lean_ctor_get(v_x_2212_, 1);
v_val_2233_ = lean_ctor_get(v_x_2212_, 2);
v_preresolved_2234_ = lean_ctor_get(v_x_2212_, 3);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_x_2212_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v_x_2212_, 0);
lean_dec(v_unused_2242_);
v___x_2236_ = v_x_2212_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_preresolved_2234_);
lean_inc(v_val_2233_);
lean_inc(v_rawVal_2232_);
lean_dec(v_x_2212_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_info_2211_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_info_2211_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_rawVal_2232_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_val_2233_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_preresolved_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2246_){
_start:
{
switch(lean_obj_tag(v_x_2246_))
{
case 2:
{
lean_object* v_info_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; 
v_info_2247_ = lean_ctor_get(v_x_2246_, 0);
v___x_2248_ = 0;
v___x_2249_ = l_Lean_SourceInfo_getPos_x3f(v_info_2247_, v___x_2248_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref_known(v_x_2246_, 2);
v___x_2250_ = lean_box(0);
return v___x_2250_;
}
else
{
lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v___x_2249_, 0);
lean_dec(v_unused_2258_);
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_x_2246_);
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_x_2246_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
case 3:
{
lean_object* v_info_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; 
v_info_2259_ = lean_ctor_get(v_x_2246_, 0);
v___x_2260_ = 0;
v___x_2261_ = l_Lean_SourceInfo_getPos_x3f(v_info_2259_, v___x_2260_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v___x_2262_; 
lean_dec_ref_known(v_x_2246_, 4);
v___x_2262_ = lean_box(0);
return v___x_2262_;
}
else
{
lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
lean_object* v_unused_2270_; 
v_unused_2270_ = lean_ctor_get(v___x_2261_, 0);
lean_dec(v_unused_2270_);
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v_x_2246_);
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_x_2246_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
case 1:
{
lean_object* v_info_2271_; 
v_info_2271_ = lean_ctor_get(v_x_2246_, 0);
if (lean_obj_tag(v_info_2271_) == 2)
{
lean_object* v_args_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; size_t v_sz_2275_; size_t v___x_2276_; lean_object* v___x_2277_; lean_object* v_fst_2278_; 
v_args_2272_ = lean_ctor_get(v_x_2246_, 2);
lean_inc_ref(v_args_2272_);
lean_dec_ref_known(v_x_2246_, 3);
v___x_2273_ = lean_box(0);
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2275_ = lean_array_size(v_args_2272_);
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2272_, v_sz_2275_, v___x_2276_, v___x_2274_);
lean_dec_ref(v_args_2272_);
v_fst_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_fst_2278_);
lean_dec_ref(v___x_2277_);
if (lean_obj_tag(v_fst_2278_) == 0)
{
return v___x_2273_;
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v_fst_2278_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v_fst_2278_, 1);
return v_val_2279_;
}
}
else
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_x_2246_);
return v___x_2280_;
}
}
default: 
{
lean_object* v___x_2281_; 
lean_dec(v_x_2246_);
v___x_2281_ = lean_box(0);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2282_, size_t v_sz_2283_, size_t v_i_2284_, lean_object* v_b_2285_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_usize_dec_lt(v_i_2284_, v_sz_2283_);
if (v___x_2286_ == 0)
{
lean_inc_ref(v_b_2285_);
return v_b_2285_;
}
else
{
lean_object* v___x_2287_; lean_object* v_a_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(0);
v_a_2288_ = lean_array_uget_borrowed(v_as_2282_, v_i_2284_);
lean_inc(v_a_2288_);
v___x_2289_ = l_Lean_Syntax_getHead_x3f(v_a_2288_);
if (lean_obj_tag(v___x_2289_) == 1)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2287_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; size_t v___x_2293_; size_t v___x_2294_; 
lean_dec(v___x_2289_);
v___x_2292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2293_ = ((size_t)1ULL);
v___x_2294_ = lean_usize_add(v_i_2284_, v___x_2293_);
v_i_2284_ = v___x_2294_;
v_b_2285_ = v___x_2292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_b_2299_){
_start:
{
size_t v_sz_boxed_2300_; size_t v_i_boxed_2301_; lean_object* v_res_2302_; 
v_sz_boxed_2300_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2301_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2296_, v_sz_boxed_2300_, v_i_boxed_2301_, v_b_2299_);
lean_dec_ref(v_b_2299_);
lean_dec_ref(v_as_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2303_, lean_object* v_source_2304_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = l_Lean_Syntax_getHeadInfo(v_source_2304_);
v___x_2306_ = l_Lean_Syntax_setHeadInfo(v_target_2303_, v___x_2305_);
v___x_2307_ = l_Lean_Syntax_getTailInfo(v_source_2304_);
v___x_2308_ = l_Lean_Syntax_setTailInfo(v___x_2306_, v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2309_, lean_object* v_source_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2309_, v_source_2310_);
lean_dec(v_source_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2312_){
_start:
{
uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = 0;
v___x_2314_ = l_Lean_SourceInfo_fromRef(v_stx_2312_, v___x_2313_);
v___x_2315_ = l_Lean_Syntax_setHeadInfo(v_stx_2312_, v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2316_, lean_object* v_withRef_2317_, lean_object* v_x_2318_, lean_object* v_oldRef_2319_){
_start:
{
lean_object* v_ref_2320_; lean_object* v___x_2321_; 
v_ref_2320_ = l_Lean_replaceRef(v_val_2316_, v_oldRef_2319_);
v___x_2321_ = lean_apply_3(v_withRef_2317_, lean_box(0), v_ref_2320_, v_x_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2322_, lean_object* v_withRef_2323_, lean_object* v_x_2324_, lean_object* v_oldRef_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2322_, v_withRef_2323_, v_x_2324_, v_oldRef_2325_);
lean_dec(v_oldRef_2325_);
lean_dec(v_val_2322_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2327_, lean_object* v_withRef_2328_, lean_object* v_toBind_2329_, lean_object* v_getRef_2330_, lean_object* v_____do__lift_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_dec(v_getRef_2330_);
lean_dec(v_toBind_2329_);
lean_dec(v_withRef_2328_);
return v_x_2327_;
}
else
{
lean_object* v_val_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v_val_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_val_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2334_, 0, v_val_2333_);
lean_closure_set(v___f_2334_, 1, v_withRef_2328_);
lean_closure_set(v___f_2334_, 2, v_x_2327_);
v___x_2335_ = lean_apply_4(v_toBind_2329_, lean_box(0), lean_box(0), v_getRef_2330_, v___f_2334_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_x_2338_){
_start:
{
lean_object* v_toBind_2339_; lean_object* v_getRef_2340_; lean_object* v_withRef_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; 
v_toBind_2339_ = lean_ctor_get(v_inst_2336_, 1);
lean_inc_n(v_toBind_2339_, 2);
lean_dec_ref(v_inst_2336_);
v_getRef_2340_ = lean_ctor_get(v_inst_2337_, 0);
lean_inc_n(v_getRef_2340_, 2);
v_withRef_2341_ = lean_ctor_get(v_inst_2337_, 1);
lean_inc(v_withRef_2341_);
lean_dec_ref(v_inst_2337_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2342_, 0, v_x_2338_);
lean_closure_set(v___f_2342_, 1, v_withRef_2341_);
lean_closure_set(v___f_2342_, 2, v_toBind_2339_);
lean_closure_set(v___f_2342_, 3, v_getRef_2340_);
v___x_2343_ = lean_apply_4(v_toBind_2339_, lean_box(0), lean_box(0), v_getRef_2340_, v___f_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_00_u03b1_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v_toBind_2349_; lean_object* v_getRef_2350_; lean_object* v_withRef_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; 
v_toBind_2349_ = lean_ctor_get(v_inst_2345_, 1);
lean_inc_n(v_toBind_2349_, 2);
lean_dec_ref(v_inst_2345_);
v_getRef_2350_ = lean_ctor_get(v_inst_2346_, 0);
lean_inc_n(v_getRef_2350_, 2);
v_withRef_2351_ = lean_ctor_get(v_inst_2346_, 1);
lean_inc(v_withRef_2351_);
lean_dec_ref(v_inst_2346_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2352_, 0, v_x_2348_);
lean_closure_set(v___f_2352_, 1, v_withRef_2351_);
lean_closure_set(v___f_2352_, 2, v_toBind_2349_);
lean_closure_set(v___f_2352_, 3, v_getRef_2350_);
v___x_2353_ = lean_apply_4(v_toBind_2349_, lean_box(0), lean_box(0), v_getRef_2350_, v___f_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2363_, lean_object* v_k_2364_){
_start:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2366_ = lean_name_eq(v_k_2364_, v___x_2365_);
if (v___x_2366_ == 0)
{
return v___x_2363_;
}
else
{
uint8_t v___x_2367_; 
v___x_2367_ = 0;
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2368_, lean_object* v_k_2369_){
_start:
{
uint8_t v___x_1982__boxed_2370_; uint8_t v_res_2371_; lean_object* v_r_2372_; 
v___x_1982__boxed_2370_ = lean_unbox(v___x_2368_);
v_res_2371_ = l_Lean_expandMacros___lam__0(v___x_1982__boxed_2370_, v_k_2369_);
lean_dec(v_k_2369_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2374_, lean_object* v_p_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
if (lean_obj_tag(v_stx_2374_) == 1)
{
lean_object* v_info_2378_; lean_object* v_kind_2379_; lean_object* v_args_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_info_2378_ = lean_ctor_get(v_stx_2374_, 0);
v_kind_2379_ = lean_ctor_get(v_stx_2374_, 1);
v_args_2380_ = lean_ctor_get(v_stx_2374_, 2);
lean_inc(v_kind_2379_);
v___x_2381_ = lean_apply_1(v_p_2375_, v_kind_2379_);
v___x_2382_ = lean_unbox(v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
lean_dec_ref(v_a_2376_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_stx_2374_);
lean_ctor_set(v___x_2383_, 1, v_a_2377_);
return v___x_2383_;
}
else
{
lean_object* v_methods_2384_; lean_object* v_quotContext_2385_; lean_object* v_currMacroScope_2386_; lean_object* v_currRecDepth_2387_; lean_object* v_maxRecDepth_2388_; lean_object* v_ref_2389_; lean_object* v_ref_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_methods_2384_ = lean_ctor_get(v_a_2376_, 0);
lean_inc_n(v_methods_2384_, 2);
v_quotContext_2385_ = lean_ctor_get(v_a_2376_, 1);
lean_inc_n(v_quotContext_2385_, 2);
v_currMacroScope_2386_ = lean_ctor_get(v_a_2376_, 2);
lean_inc_n(v_currMacroScope_2386_, 2);
v_currRecDepth_2387_ = lean_ctor_get(v_a_2376_, 3);
lean_inc_n(v_currRecDepth_2387_, 2);
v_maxRecDepth_2388_ = lean_ctor_get(v_a_2376_, 4);
lean_inc_n(v_maxRecDepth_2388_, 2);
v_ref_2389_ = lean_ctor_get(v_a_2376_, 5);
lean_inc(v_ref_2389_);
lean_dec_ref(v_a_2376_);
v_ref_2390_ = l_Lean_replaceRef(v_stx_2374_, v_ref_2389_);
lean_dec(v_ref_2389_);
lean_inc(v_ref_2390_);
v___x_2391_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2391_, 0, v_methods_2384_);
lean_ctor_set(v___x_2391_, 1, v_quotContext_2385_);
lean_ctor_set(v___x_2391_, 2, v_currMacroScope_2386_);
lean_ctor_set(v___x_2391_, 3, v_currRecDepth_2387_);
lean_ctor_set(v___x_2391_, 4, v_maxRecDepth_2388_);
lean_ctor_set(v___x_2391_, 5, v_ref_2390_);
lean_inc_ref(v_stx_2374_);
v___x_2392_ = l_Lean_Macro_expandMacro_x3f(v_stx_2374_, v___x_2391_, v_a_2377_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
if (lean_obj_tag(v_a_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref_known(v___x_2391_, 6);
v_a_2394_ = lean_ctor_get(v___x_2392_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v___x_2392_, 0);
lean_dec(v_unused_2440_);
v___x_2396_ = v___x_2392_;
v_isShared_2397_ = v_isSharedCheck_2439_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2439_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
uint8_t v___x_2398_; 
v___x_2398_ = lean_nat_dec_eq(v_currRecDepth_2387_, v_maxRecDepth_2388_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2430_; 
lean_inc_ref(v_args_2380_);
lean_inc(v_kind_2379_);
lean_inc(v_info_2378_);
lean_del_object(v___x_2396_);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_stx_2374_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; 
v_unused_2431_ = lean_ctor_get(v_stx_2374_, 2);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_stx_2374_, 1);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_stx_2374_, 0);
lean_dec(v_unused_2433_);
v___x_2400_ = v_stx_2374_;
v_isShared_2401_ = v_isSharedCheck_2430_;
goto v_resetjp_2399_;
}
else
{
lean_dec(v_stx_2374_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2430_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; size_t v_sz_2405_; size_t v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; 
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_add(v_currRecDepth_2387_, v___x_2402_);
lean_dec(v_currRecDepth_2387_);
v___x_2404_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2404_, 0, v_methods_2384_);
lean_ctor_set(v___x_2404_, 1, v_quotContext_2385_);
lean_ctor_set(v___x_2404_, 2, v_currMacroScope_2386_);
lean_ctor_set(v___x_2404_, 3, v___x_2403_);
lean_ctor_set(v___x_2404_, 4, v_maxRecDepth_2388_);
lean_ctor_set(v___x_2404_, 5, v_ref_2390_);
v_sz_2405_ = lean_array_size(v_args_2380_);
v___x_2406_ = ((size_t)0ULL);
v___x_2407_ = lean_unbox(v___x_2381_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2407_, v_sz_2405_, v___x_2406_, v_args_2380_, v___x_2404_, v_a_2394_);
lean_dec_ref_known(v___x_2404_, 6);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2420_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_a_2410_ = lean_ctor_get(v___x_2408_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2412_ = v___x_2408_;
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 2, v_a_2409_);
v___x_2415_ = v___x_2400_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_info_2378_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_kind_2379_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_a_2409_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2415_);
v___x_2417_ = v___x_2412_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_a_2410_);
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
else
{
lean_object* v_a_2421_; lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_del_object(v___x_2400_);
lean_dec(v_kind_2379_);
lean_dec(v_info_2378_);
v_a_2421_ = lean_ctor_get(v___x_2408_, 0);
v_a_2422_ = lean_ctor_get(v___x_2408_, 1);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2408_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_inc(v_a_2421_);
lean_dec(v___x_2408_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2421_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_ref_2390_);
lean_dec(v_maxRecDepth_2388_);
lean_dec(v_currRecDepth_2387_);
lean_dec(v_currMacroScope_2386_);
lean_dec(v_quotContext_2385_);
lean_dec(v_methods_2384_);
v___x_2434_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_stx_2374_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2435_);
v___x_2437_ = v___x_2396_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_a_2394_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v_val_2442_; lean_object* v___f_2443_; 
lean_dec(v_ref_2390_);
lean_dec(v_maxRecDepth_2388_);
lean_dec(v_currRecDepth_2387_);
lean_dec(v_currMacroScope_2386_);
lean_dec(v_quotContext_2385_);
lean_dec(v_methods_2384_);
lean_dec_ref_known(v_stx_2374_, 3);
v_a_2441_ = lean_ctor_get(v___x_2392_, 1);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2392_, 2);
v_val_2442_ = lean_ctor_get(v_a_2393_, 0);
lean_inc(v_val_2442_);
lean_dec_ref_known(v_a_2393_, 1);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2443_, 0, v___x_2381_);
v_stx_2374_ = v_val_2442_;
v_p_2375_ = v___f_2443_;
v_a_2376_ = v___x_2391_;
v_a_2377_ = v_a_2441_;
goto _start;
}
}
else
{
lean_object* v_a_2445_; lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref_known(v___x_2391_, 6);
lean_dec(v_ref_2390_);
lean_dec(v_maxRecDepth_2388_);
lean_dec(v_currRecDepth_2387_);
lean_dec(v_currMacroScope_2386_);
lean_dec(v_quotContext_2385_);
lean_dec(v_methods_2384_);
lean_dec_ref_known(v_stx_2374_, 3);
v_a_2445_ = lean_ctor_get(v___x_2392_, 0);
v_a_2446_ = lean_ctor_get(v___x_2392_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2392_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_inc(v_a_2445_);
lean_dec(v___x_2392_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2445_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
else
{
lean_object* v___x_2454_; 
lean_dec_ref(v_a_2376_);
lean_dec_ref(v_p_2375_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_stx_2374_);
lean_ctor_set(v___x_2454_, 1, v_a_2377_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2455_, size_t v_sz_2456_, size_t v_i_2457_, lean_object* v_bs_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_lt(v_i_2457_, v_sz_2456_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_bs_2458_);
lean_ctor_set(v___x_2462_, 1, v___y_2460_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v_v_2465_; lean_object* v___x_2466_; 
v___x_2463_ = lean_box(v___x_2455_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
v_v_2465_ = lean_array_uget_borrowed(v_bs_2458_, v_i_2457_);
lean_inc_ref(v___y_2459_);
lean_inc(v_v_2465_);
v___x_2466_ = l_Lean_expandMacros(v_v_2465_, v___f_2464_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v_bs_x27_2470_; size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
v_a_2468_ = lean_ctor_get(v___x_2466_, 1);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2466_, 2);
v___x_2469_ = lean_unsigned_to_nat(0u);
v_bs_x27_2470_ = lean_array_uset(v_bs_2458_, v_i_2457_, v___x_2469_);
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = lean_usize_add(v_i_2457_, v___x_2471_);
v___x_2473_ = lean_array_uset(v_bs_x27_2470_, v_i_2457_, v_a_2467_);
v_i_2457_ = v___x_2472_;
v_bs_2458_ = v___x_2473_;
v___y_2460_ = v_a_2468_;
goto _start;
}
else
{
lean_object* v_a_2475_; lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_bs_2458_);
v_a_2475_ = lean_ctor_get(v___x_2466_, 0);
v_a_2476_ = lean_ctor_get(v___x_2466_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2466_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_inc(v_a_2475_);
lean_dec(v___x_2466_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2475_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2484_, lean_object* v_sz_2485_, lean_object* v_i_2486_, lean_object* v_bs_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v___x_2001__boxed_2490_; size_t v_sz_boxed_2491_; size_t v_i_boxed_2492_; lean_object* v_res_2493_; 
v___x_2001__boxed_2490_ = lean_unbox(v___x_2484_);
v_sz_boxed_2491_ = lean_unbox_usize(v_sz_2485_);
lean_dec(v_sz_2485_);
v_i_boxed_2492_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2001__boxed_2490_, v_sz_boxed_2491_, v_i_boxed_2492_, v_bs_2487_, v___y_2488_, v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2494_, lean_object* v_val_2495_, uint8_t v_canonical_2496_){
_start:
{
lean_object* v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2497_ = l_Lean_SourceInfo_fromRef(v_src_2494_, v_canonical_2496_);
v___x_2498_ = 1;
lean_inc(v_val_2495_);
v___x_2499_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2495_, v___x_2498_);
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_string_utf8_byte_size(v___x_2499_);
v___x_2502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2499_);
lean_ctor_set(v___x_2502_, 1, v___x_2500_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2497_);
lean_ctor_set(v___x_2504_, 1, v___x_2502_);
lean_ctor_set(v___x_2504_, 2, v_val_2495_);
lean_ctor_set(v___x_2504_, 3, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2505_, lean_object* v_val_2506_, lean_object* v_canonical_2507_){
_start:
{
uint8_t v_canonical_boxed_2508_; lean_object* v_res_2509_; 
v_canonical_boxed_2508_ = lean_unbox(v_canonical_2507_);
v_res_2509_ = l_Lean_mkIdentFrom(v_src_2505_, v_val_2506_, v_canonical_boxed_2508_);
lean_dec(v_src_2505_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2510_, uint8_t v_canonical_2511_, lean_object* v_toPure_2512_, lean_object* v_____do__lift_2513_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = l_Lean_mkIdentFrom(v_____do__lift_2513_, v_val_2510_, v_canonical_2511_);
v___x_2515_ = lean_apply_2(v_toPure_2512_, lean_box(0), v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2516_, lean_object* v_canonical_2517_, lean_object* v_toPure_2518_, lean_object* v_____do__lift_2519_){
_start:
{
uint8_t v_canonical_boxed_2520_; lean_object* v_res_2521_; 
v_canonical_boxed_2520_ = lean_unbox(v_canonical_2517_);
v_res_2521_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2516_, v_canonical_boxed_2520_, v_toPure_2518_, v_____do__lift_2519_);
lean_dec(v_____do__lift_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_val_2524_, uint8_t v_canonical_2525_){
_start:
{
lean_object* v_toApplicative_2526_; lean_object* v_toBind_2527_; lean_object* v_getRef_2528_; lean_object* v_toPure_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; 
v_toApplicative_2526_ = lean_ctor_get(v_inst_2522_, 0);
lean_inc_ref(v_toApplicative_2526_);
v_toBind_2527_ = lean_ctor_get(v_inst_2522_, 1);
lean_inc(v_toBind_2527_);
lean_dec_ref(v_inst_2522_);
v_getRef_2528_ = lean_ctor_get(v_inst_2523_, 0);
lean_inc(v_getRef_2528_);
lean_dec_ref(v_inst_2523_);
v_toPure_2529_ = lean_ctor_get(v_toApplicative_2526_, 1);
lean_inc(v_toPure_2529_);
lean_dec_ref(v_toApplicative_2526_);
v___x_2530_ = lean_box(v_canonical_2525_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2531_, 0, v_val_2524_);
lean_closure_set(v___f_2531_, 1, v___x_2530_);
lean_closure_set(v___f_2531_, 2, v_toPure_2529_);
v___x_2532_ = lean_apply_4(v_toBind_2527_, lean_box(0), lean_box(0), v_getRef_2528_, v___f_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_val_2535_, lean_object* v_canonical_2536_){
_start:
{
uint8_t v_canonical_boxed_2537_; lean_object* v_res_2538_; 
v_canonical_boxed_2537_ = lean_unbox(v_canonical_2536_);
v_res_2538_ = l_Lean_mkIdentFromRef___redArg(v_inst_2533_, v_inst_2534_, v_val_2535_, v_canonical_boxed_2537_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_val_2542_, uint8_t v_canonical_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_mkIdentFromRef___redArg(v_inst_2540_, v_inst_2541_, v_val_2542_, v_canonical_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_val_2548_, lean_object* v_canonical_2549_){
_start:
{
uint8_t v_canonical_boxed_2550_; lean_object* v_res_2551_; 
v_canonical_boxed_2550_ = lean_unbox(v_canonical_2549_);
v_res_2551_ = l_Lean_mkIdentFromRef(v_m_2545_, v_inst_2546_, v_inst_2547_, v_val_2548_, v_canonical_boxed_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2555_, lean_object* v_c_2556_, uint8_t v_canonical_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_id_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2558_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2559_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2556_);
v_id_2560_ = l_Lean_addMacroScope(v___x_2558_, v_c_2556_, v___x_2559_);
v___x_2561_ = l_Lean_SourceInfo_fromRef(v_src_2555_, v_canonical_2557_);
v___x_2562_ = 1;
lean_inc(v_id_2560_);
v___x_2563_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2560_, v___x_2562_);
v___x_2564_ = lean_string_utf8_byte_size(v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2559_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_c_2556_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2566_);
v___x_2569_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2561_);
lean_ctor_set(v___x_2569_, 1, v___x_2565_);
lean_ctor_set(v___x_2569_, 2, v_id_2560_);
lean_ctor_set(v___x_2569_, 3, v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2570_, lean_object* v_c_2571_, lean_object* v_canonical_2572_){
_start:
{
uint8_t v_canonical_boxed_2573_; lean_object* v_res_2574_; 
v_canonical_boxed_2573_ = lean_unbox(v_canonical_2572_);
v_res_2574_ = l_Lean_mkCIdentFrom(v_src_2570_, v_c_2571_, v_canonical_boxed_2573_);
lean_dec(v_src_2570_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2575_, uint8_t v_canonical_2576_, lean_object* v_toPure_2577_, lean_object* v_____do__lift_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = l_Lean_mkCIdentFrom(v_____do__lift_2578_, v_c_2575_, v_canonical_2576_);
v___x_2580_ = lean_apply_2(v_toPure_2577_, lean_box(0), v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2581_, lean_object* v_canonical_2582_, lean_object* v_toPure_2583_, lean_object* v_____do__lift_2584_){
_start:
{
uint8_t v_canonical_boxed_2585_; lean_object* v_res_2586_; 
v_canonical_boxed_2585_ = lean_unbox(v_canonical_2582_);
v_res_2586_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2581_, v_canonical_boxed_2585_, v_toPure_2583_, v_____do__lift_2584_);
lean_dec(v_____do__lift_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_c_2589_, uint8_t v_canonical_2590_){
_start:
{
lean_object* v_toApplicative_2591_; lean_object* v_toBind_2592_; lean_object* v_getRef_2593_; lean_object* v_toPure_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; 
v_toApplicative_2591_ = lean_ctor_get(v_inst_2587_, 0);
lean_inc_ref(v_toApplicative_2591_);
v_toBind_2592_ = lean_ctor_get(v_inst_2587_, 1);
lean_inc(v_toBind_2592_);
lean_dec_ref(v_inst_2587_);
v_getRef_2593_ = lean_ctor_get(v_inst_2588_, 0);
lean_inc(v_getRef_2593_);
lean_dec_ref(v_inst_2588_);
v_toPure_2594_ = lean_ctor_get(v_toApplicative_2591_, 1);
lean_inc(v_toPure_2594_);
lean_dec_ref(v_toApplicative_2591_);
v___x_2595_ = lean_box(v_canonical_2590_);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2596_, 0, v_c_2589_);
lean_closure_set(v___f_2596_, 1, v___x_2595_);
lean_closure_set(v___f_2596_, 2, v_toPure_2594_);
v___x_2597_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v_getRef_2593_, v___f_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_c_2600_, lean_object* v_canonical_2601_){
_start:
{
uint8_t v_canonical_boxed_2602_; lean_object* v_res_2603_; 
v_canonical_boxed_2602_ = lean_unbox(v_canonical_2601_);
v_res_2603_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2598_, v_inst_2599_, v_c_2600_, v_canonical_boxed_2602_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_c_2607_, uint8_t v_canonical_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2605_, v_inst_2606_, v_c_2607_, v_canonical_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_c_2613_, lean_object* v_canonical_2614_){
_start:
{
uint8_t v_canonical_boxed_2615_; lean_object* v_res_2616_; 
v_canonical_boxed_2615_ = lean_unbox(v_canonical_2614_);
v_res_2616_ = l_Lean_mkCIdentFromRef(v_m_2610_, v_inst_2611_, v_inst_2612_, v_c_2613_, v_canonical_boxed_2615_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_box(0);
v___x_2619_ = 0;
v___x_2620_ = l_Lean_mkCIdentFrom(v___x_2618_, v_c_2617_, v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2621_){
_start:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2622_ = lean_box(2);
v___x_2623_ = 1;
lean_inc(v_val_2621_);
v___x_2624_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2621_, v___x_2623_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_string_utf8_byte_size(v___x_2624_);
v___x_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2624_);
lean_ctor_set(v___x_2627_, 1, v___x_2625_);
lean_ctor_set(v___x_2627_, 2, v___x_2626_);
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2622_);
lean_ctor_set(v___x_2629_, 1, v___x_2627_);
lean_ctor_set(v___x_2629_, 2, v_val_2621_);
lean_ctor_set(v___x_2629_, 3, v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2635_ = lean_box(2);
v___x_2636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v_args_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2637_, lean_object* v_as_2638_, size_t v_sz_2639_, size_t v_i_2640_, lean_object* v_b_2641_){
_start:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_lt(v_i_2640_, v_sz_2639_);
if (v___x_2642_ == 0)
{
lean_dec(v_sep_2637_);
return v_b_2641_;
}
else
{
lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2664_; 
v_fst_2643_ = lean_ctor_get(v_b_2641_, 0);
v_snd_2644_ = lean_ctor_get(v_b_2641_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_b_2641_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2646_ = v_b_2641_;
v_isShared_2647_ = v_isSharedCheck_2664_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_snd_2644_);
lean_inc(v_fst_2643_);
lean_dec(v_b_2641_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2664_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_r_2649_; lean_object* v_i_2658_; lean_object* v_a_2659_; uint8_t v___x_2660_; 
v_i_2658_ = lean_unsigned_to_nat(0u);
v_a_2659_ = lean_array_uget_borrowed(v_as_2638_, v_i_2640_);
v___x_2660_ = lean_nat_dec_lt(v_i_2658_, v_fst_2643_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; 
lean_inc(v_a_2659_);
v___x_2661_ = lean_array_push(v_snd_2644_, v_a_2659_);
v_r_2649_ = v___x_2661_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_inc(v_sep_2637_);
v___x_2662_ = lean_array_push(v_snd_2644_, v_sep_2637_);
lean_inc(v_a_2659_);
v___x_2663_ = lean_array_push(v___x_2662_, v_a_2659_);
v_r_2649_ = v___x_2663_;
goto v___jp_2648_;
}
v___jp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = lean_unsigned_to_nat(1u);
v___x_2651_ = lean_nat_add(v_fst_2643_, v___x_2650_);
lean_dec(v_fst_2643_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v_r_2649_);
lean_ctor_set(v___x_2646_, 0, v___x_2651_);
v___x_2653_ = v___x_2646_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_r_2649_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
size_t v___x_2654_; size_t v___x_2655_; 
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_add(v_i_2640_, v___x_2654_);
v_i_2640_ = v___x_2655_;
v_b_2641_ = v___x_2653_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2665_, lean_object* v_as_2666_, lean_object* v_sz_2667_, lean_object* v_i_2668_, lean_object* v_b_2669_){
_start:
{
size_t v_sz_boxed_2670_; size_t v_i_boxed_2671_; lean_object* v_res_2672_; 
v_sz_boxed_2670_ = lean_unbox_usize(v_sz_2667_);
lean_dec(v_sz_2667_);
v_i_boxed_2671_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2665_, v_as_2666_, v_sz_boxed_2670_, v_i_boxed_2671_, v_b_2669_);
lean_dec_ref(v_as_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2678_, lean_object* v_sep_2679_){
_start:
{
lean_object* v___x_2680_; size_t v_sz_2681_; size_t v___x_2682_; lean_object* v___x_2683_; lean_object* v_snd_2684_; 
v___x_2680_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2681_ = lean_array_size(v_as_2678_);
v___x_2682_ = ((size_t)0ULL);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2679_, v_as_2678_, v_sz_2681_, v___x_2682_, v___x_2680_);
v_snd_2684_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_snd_2684_);
lean_dec_ref(v___x_2683_);
return v_snd_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2685_, lean_object* v_sep_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_mkSepArray(v_as_2685_, v_sep_2686_);
lean_dec_ref(v_as_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2695_){
_start:
{
if (lean_obj_tag(v_arg_2695_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2696_;
}
else
{
lean_object* v_val_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_val_2697_ = lean_ctor_get(v_arg_2695_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v_arg_2695_, 1);
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_mk_empty_array_with_capacity(v___x_2698_);
v___x_2700_ = lean_array_push(v___x_2699_, v_val_2697_);
v___x_2701_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2702_ = lean_box(2);
v___x_2703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2701_);
lean_ctor_set(v___x_2703_, 2, v___x_2700_);
return v___x_2703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2710_, uint8_t v_canonical_2711_){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2712_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2713_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2714_ = l_Lean_mkAtomFrom(v_ref_2710_, v___x_2713_, v_canonical_2711_);
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_mk_empty_array_with_capacity(v___x_2715_);
v___x_2717_ = lean_array_push(v___x_2716_, v___x_2714_);
v___x_2718_ = lean_box(2);
v___x_2719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v___x_2712_);
lean_ctor_set(v___x_2719_, 2, v___x_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2720_, lean_object* v_canonical_2721_){
_start:
{
uint8_t v_canonical_boxed_2722_; lean_object* v_res_2723_; 
v_canonical_boxed_2722_ = lean_unbox(v_canonical_2721_);
v_res_2723_ = l_Lean_mkHole(v_ref_2720_, v_canonical_boxed_2722_);
lean_dec(v_ref_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2724_, lean_object* v_sep_2725_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = l_Lean_mkSepArray(v_a_2724_, v_sep_2725_);
v___x_2727_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2728_ = lean_box(2);
v___x_2729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
lean_ctor_set(v___x_2729_, 2, v___x_2726_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2730_, lean_object* v_sep_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Syntax_mkSep(v_a_2730_, v_sep_2731_);
lean_dec_ref(v_a_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2739_, lean_object* v_elems_2740_){
_start:
{
uint8_t v___x_2741_; 
lean_inc_ref(v_sep_2739_);
v___x_2741_ = lean_string_isempty(v_sep_2739_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = l_Lean_mkAtom(v_sep_2739_);
v___x_2743_ = l_Lean_mkSepArray(v_elems_2740_, v___x_2742_);
return v___x_2743_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_sep_2739_);
v___x_2744_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2745_ = l_Lean_mkSepArray(v_elems_2740_, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2746_, lean_object* v_elems_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2746_, v_elems_2747_);
lean_dec_ref(v_elems_2747_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2749_, lean_object* v_toPure_2750_, lean_object* v_sep_2751_, lean_object* v_ref_2752_){
_start:
{
lean_object* v___y_2754_; uint8_t v___x_2757_; 
lean_inc_ref(v_sep_2751_);
v___x_2757_ = lean_string_isempty(v_sep_2751_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_mkAtomFrom(v_ref_2752_, v_sep_2751_, v___x_2757_);
v___y_2754_ = v___x_2758_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2759_; 
lean_dec_ref(v_sep_2751_);
v___x_2759_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2754_ = v___x_2759_;
goto v___jp_2753_;
}
v___jp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = l_Lean_mkSepArray(v_elems_2749_, v___y_2754_);
v___x_2756_ = lean_apply_2(v_toPure_2750_, lean_box(0), v___x_2755_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2760_, lean_object* v_toPure_2761_, lean_object* v_sep_2762_, lean_object* v_ref_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2760_, v_toPure_2761_, v_sep_2762_, v_ref_2763_);
lean_dec(v_ref_2763_);
lean_dec_ref(v_elems_2760_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_sep_2767_, lean_object* v_elems_2768_){
_start:
{
lean_object* v_toApplicative_2769_; lean_object* v_toBind_2770_; lean_object* v_getRef_2771_; lean_object* v_toPure_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; 
v_toApplicative_2769_ = lean_ctor_get(v_inst_2765_, 0);
lean_inc_ref(v_toApplicative_2769_);
v_toBind_2770_ = lean_ctor_get(v_inst_2765_, 1);
lean_inc(v_toBind_2770_);
lean_dec_ref(v_inst_2765_);
v_getRef_2771_ = lean_ctor_get(v_inst_2766_, 0);
lean_inc(v_getRef_2771_);
lean_dec_ref(v_inst_2766_);
v_toPure_2772_ = lean_ctor_get(v_toApplicative_2769_, 1);
lean_inc(v_toPure_2772_);
lean_dec_ref(v_toApplicative_2769_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2773_, 0, v_elems_2768_);
lean_closure_set(v___f_2773_, 1, v_toPure_2772_);
lean_closure_set(v___f_2773_, 2, v_sep_2767_);
v___x_2774_ = lean_apply_4(v_toBind_2770_, lean_box(0), lean_box(0), v_getRef_2771_, v___f_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_sep_2778_, lean_object* v_elems_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2776_, v_inst_2777_, v_sep_2778_, v_elems_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object* v_sep_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(v___x_2782_, 0, v_sep_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2783_, lean_object* v_elems_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2783_, v_elems_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2786_, lean_object* v_elems_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2786_, v_elems_2787_);
lean_dec_ref(v_elems_2787_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2789_, lean_object* v_sep_2790_, lean_object* v_elems_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2790_, v_elems_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2793_, lean_object* v_sep_2794_, lean_object* v_elems_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2793_, v_sep_2794_, v_elems_2795_);
lean_dec_ref(v_elems_2795_);
lean_dec(v_k_2793_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2797_, lean_object* v_sep_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2799_, 0, v_k_2797_);
lean_closure_set(v___x_2799_, 1, v_sep_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2808_ = lean_array_get_size(v_x_2807_);
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = lean_nat_dec_eq(v___x_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2811_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2812_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2813_ = lean_box(2);
v___x_2814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2812_);
lean_ctor_set(v___x_2814_, 2, v_x_2807_);
v___x_2815_ = lean_unsigned_to_nat(2u);
v___x_2816_ = lean_mk_empty_array_with_capacity(v___x_2815_);
v___x_2817_ = lean_array_push(v___x_2816_, v_fn_2806_);
v___x_2818_ = lean_array_push(v___x_2817_, v___x_2814_);
v___x_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2813_);
lean_ctor_set(v___x_2819_, 1, v___x_2811_);
lean_ctor_set(v___x_2819_, 2, v___x_2818_);
return v___x_2819_;
}
else
{
lean_dec_ref(v_x_2807_);
return v_fn_2806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2820_, lean_object* v_args_2821_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = l_Lean_mkCIdent(v_fn_2820_);
v___x_2823_ = l_Lean_Syntax_mkApp(v___x_2822_, v_args_2821_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2824_, lean_object* v_val_2825_, lean_object* v_info_2826_){
_start:
{
lean_object* v_atom_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_atom_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2827_, 0, v_info_2826_);
lean_ctor_set(v_atom_2827_, 1, v_val_2825_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_mk_empty_array_with_capacity(v___x_2828_);
v___x_2830_ = lean_array_push(v___x_2829_, v_atom_2827_);
v___x_2831_ = lean_box(2);
v___x_2832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v_kind_2824_);
lean_ctor_set(v___x_2832_, 2, v___x_2830_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2836_, lean_object* v_info_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2839_ = l_Char_quote(v_val_2836_);
v___x_2840_ = l_Lean_Syntax_mkLit(v___x_2838_, v___x_2839_, v_info_2837_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2841_, lean_object* v_info_2842_){
_start:
{
uint32_t v_val_boxed_2843_; lean_object* v_res_2844_; 
v_val_boxed_2843_ = lean_unbox_uint32(v_val_2841_);
lean_dec(v_val_2841_);
v_res_2844_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2843_, v_info_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2848_, lean_object* v_info_2849_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2851_ = l_String_quote(v_val_2848_);
v___x_2852_ = l_Lean_Syntax_mkLit(v___x_2850_, v___x_2851_, v_info_2849_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2856_, lean_object* v_info_2857_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2859_ = l_Lean_Syntax_mkLit(v___x_2858_, v_val_2856_, v_info_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2860_, lean_object* v_info_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2863_ = l_Nat_reprFast(v_val_2860_);
v___x_2864_ = l_Lean_Syntax_mkLit(v___x_2862_, v___x_2863_, v_info_2861_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2868_, lean_object* v_info_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2871_ = l_Lean_Syntax_mkLit(v___x_2870_, v_val_2868_, v_info_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2875_, lean_object* v_info_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2878_ = l_Lean_Syntax_mkLit(v___x_2877_, v_val_2875_, v_info_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2879_, lean_object* v_i_2880_, lean_object* v_val_2881_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_string_utf8_at_end(v_s_2879_, v_i_2880_);
if (v___x_2882_ == 0)
{
uint32_t v_c_2883_; uint32_t v___x_2884_; uint8_t v___x_2885_; 
v_c_2883_ = lean_string_utf8_get(v_s_2879_, v_i_2880_);
v___x_2884_ = 48;
v___x_2885_ = lean_uint32_dec_eq(v_c_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
uint32_t v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = 49;
v___x_2887_ = lean_uint32_dec_eq(v_c_2883_, v___x_2886_);
if (v___x_2887_ == 0)
{
uint32_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = 95;
v___x_2889_ = lean_uint32_dec_eq(v_c_2883_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v_val_2881_);
lean_dec(v_i_2880_);
v___x_2890_ = lean_box(0);
return v___x_2890_;
}
else
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_string_utf8_next(v_s_2879_, v_i_2880_);
lean_dec(v_i_2880_);
v_i_2880_ = v___x_2891_;
goto _start;
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2893_ = lean_string_utf8_next(v_s_2879_, v_i_2880_);
lean_dec(v_i_2880_);
v___x_2894_ = lean_unsigned_to_nat(2u);
v___x_2895_ = lean_nat_mul(v___x_2894_, v_val_2881_);
lean_dec(v_val_2881_);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_nat_add(v___x_2895_, v___x_2896_);
lean_dec(v___x_2895_);
v_i_2880_ = v___x_2893_;
v_val_2881_ = v___x_2897_;
goto _start;
}
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_string_utf8_next(v_s_2879_, v_i_2880_);
lean_dec(v_i_2880_);
v___x_2900_ = lean_unsigned_to_nat(2u);
v___x_2901_ = lean_nat_mul(v___x_2900_, v_val_2881_);
lean_dec(v_val_2881_);
v_i_2880_ = v___x_2899_;
v_val_2881_ = v___x_2901_;
goto _start;
}
}
else
{
lean_object* v___x_2903_; 
lean_dec(v_i_2880_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_val_2881_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2904_, lean_object* v_i_2905_, lean_object* v_val_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2904_, v_i_2905_, v_val_2906_);
lean_dec_ref(v_s_2904_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2908_, lean_object* v_i_2909_, lean_object* v_val_2910_){
_start:
{
uint8_t v___x_2911_; 
v___x_2911_ = lean_string_utf8_at_end(v_s_2908_, v_i_2909_);
if (v___x_2911_ == 0)
{
uint32_t v_c_2912_; uint8_t v___y_2914_; uint32_t v___x_2928_; uint8_t v___x_2929_; 
v_c_2912_ = lean_string_utf8_get(v_s_2908_, v_i_2909_);
v___x_2928_ = 48;
v___x_2929_ = lean_uint32_dec_le(v___x_2928_, v_c_2912_);
if (v___x_2929_ == 0)
{
v___y_2914_ = v___x_2929_;
goto v___jp_2913_;
}
else
{
uint32_t v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = 55;
v___x_2931_ = lean_uint32_dec_le(v_c_2912_, v___x_2930_);
v___y_2914_ = v___x_2931_;
goto v___jp_2913_;
}
v___jp_2913_:
{
if (v___y_2914_ == 0)
{
uint32_t v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = 95;
v___x_2916_ = lean_uint32_dec_eq(v_c_2912_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_dec(v_val_2910_);
lean_dec(v_i_2909_);
v___x_2917_ = lean_box(0);
return v___x_2917_;
}
else
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_string_utf8_next(v_s_2908_, v_i_2909_);
lean_dec(v_i_2909_);
v_i_2909_ = v___x_2918_;
goto _start;
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2920_ = lean_string_utf8_next(v_s_2908_, v_i_2909_);
lean_dec(v_i_2909_);
v___x_2921_ = lean_unsigned_to_nat(8u);
v___x_2922_ = lean_nat_mul(v___x_2921_, v_val_2910_);
lean_dec(v_val_2910_);
v___x_2923_ = lean_uint32_to_nat(v_c_2912_);
v___x_2924_ = lean_nat_add(v___x_2922_, v___x_2923_);
lean_dec(v___x_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_unsigned_to_nat(48u);
v___x_2926_ = lean_nat_sub(v___x_2924_, v___x_2925_);
lean_dec(v___x_2924_);
v_i_2909_ = v___x_2920_;
v_val_2910_ = v___x_2926_;
goto _start;
}
}
}
else
{
lean_object* v___x_2932_; 
lean_dec(v_i_2909_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_val_2910_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2933_, lean_object* v_i_2934_, lean_object* v_val_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2933_, v_i_2934_, v_val_2935_);
lean_dec_ref(v_s_2933_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2937_, lean_object* v_i_2938_){
_start:
{
uint32_t v_c_2939_; lean_object* v_i_2940_; uint8_t v___y_2942_; uint8_t v___y_2952_; uint8_t v___y_2965_; uint32_t v___x_2975_; uint8_t v___x_2976_; 
v_c_2939_ = lean_string_utf8_get(v_s_2937_, v_i_2938_);
v_i_2940_ = lean_string_utf8_next(v_s_2937_, v_i_2938_);
v___x_2975_ = 48;
v___x_2976_ = lean_uint32_dec_le(v___x_2975_, v_c_2939_);
if (v___x_2976_ == 0)
{
v___y_2965_ = v___x_2976_;
goto v___jp_2964_;
}
else
{
uint32_t v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = 57;
v___x_2978_ = lean_uint32_dec_le(v_c_2939_, v___x_2977_);
v___y_2965_ = v___x_2978_;
goto v___jp_2964_;
}
v___jp_2941_:
{
if (v___y_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_i_2940_);
v___x_2943_ = lean_box(0);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2944_ = lean_unsigned_to_nat(10u);
v___x_2945_ = lean_uint32_to_nat(v_c_2939_);
v___x_2946_ = lean_nat_add(v___x_2944_, v___x_2945_);
lean_dec(v___x_2945_);
v___x_2947_ = lean_unsigned_to_nat(65u);
v___x_2948_ = lean_nat_sub(v___x_2946_, v___x_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_i_2940_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
v___jp_2951_:
{
if (v___y_2952_ == 0)
{
uint32_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = 65;
v___x_2954_ = lean_uint32_dec_le(v___x_2953_, v_c_2939_);
if (v___x_2954_ == 0)
{
v___y_2942_ = v___x_2954_;
goto v___jp_2941_;
}
else
{
uint32_t v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = 70;
v___x_2956_ = lean_uint32_dec_le(v_c_2939_, v___x_2955_);
v___y_2942_ = v___x_2956_;
goto v___jp_2941_;
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2957_ = lean_unsigned_to_nat(10u);
v___x_2958_ = lean_uint32_to_nat(v_c_2939_);
v___x_2959_ = lean_nat_add(v___x_2957_, v___x_2958_);
lean_dec(v___x_2958_);
v___x_2960_ = lean_unsigned_to_nat(97u);
v___x_2961_ = lean_nat_sub(v___x_2959_, v___x_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_i_2940_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
v___jp_2964_:
{
if (v___y_2965_ == 0)
{
uint32_t v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = 97;
v___x_2967_ = lean_uint32_dec_le(v___x_2966_, v_c_2939_);
if (v___x_2967_ == 0)
{
v___y_2952_ = v___x_2967_;
goto v___jp_2951_;
}
else
{
uint32_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = 102;
v___x_2969_ = lean_uint32_dec_le(v_c_2939_, v___x_2968_);
v___y_2952_ = v___x_2969_;
goto v___jp_2951_;
}
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2970_ = lean_uint32_to_nat(v_c_2939_);
v___x_2971_ = lean_unsigned_to_nat(48u);
v___x_2972_ = lean_nat_sub(v___x_2970_, v___x_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_i_2940_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2979_, lean_object* v_i_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2979_, v_i_2980_);
lean_dec(v_i_2980_);
lean_dec_ref(v_s_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2982_, lean_object* v_i_2983_, lean_object* v_val_2984_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_string_utf8_at_end(v_s_2982_, v_i_2983_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2982_, v_i_2983_);
if (lean_obj_tag(v___x_2986_) == 0)
{
uint32_t v___x_2987_; uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_string_utf8_get(v_s_2982_, v_i_2983_);
v___x_2988_ = 95;
v___x_2989_ = lean_uint32_dec_eq(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec(v_val_2984_);
lean_dec(v_i_2983_);
v___x_2990_ = lean_box(0);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_string_utf8_next(v_s_2982_, v_i_2983_);
lean_dec(v_i_2983_);
v_i_2983_ = v___x_2991_;
goto _start;
}
}
else
{
lean_object* v_val_2993_; lean_object* v_fst_2994_; lean_object* v_snd_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_i_2983_);
v_val_2993_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v___x_2986_, 1);
v_fst_2994_ = lean_ctor_get(v_val_2993_, 0);
lean_inc(v_fst_2994_);
v_snd_2995_ = lean_ctor_get(v_val_2993_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_val_2993_);
v___x_2996_ = lean_unsigned_to_nat(16u);
v___x_2997_ = lean_nat_mul(v___x_2996_, v_val_2984_);
lean_dec(v_val_2984_);
v___x_2998_ = lean_nat_add(v___x_2997_, v_fst_2994_);
lean_dec(v_fst_2994_);
lean_dec(v___x_2997_);
v_i_2983_ = v_snd_2995_;
v_val_2984_ = v___x_2998_;
goto _start;
}
}
else
{
lean_object* v___x_3000_; 
lean_dec(v_i_2983_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_val_2984_);
return v___x_3000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3001_, lean_object* v_i_3002_, lean_object* v_val_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3001_, v_i_3002_, v_val_3003_);
lean_dec_ref(v_s_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3005_, lean_object* v_i_3006_, lean_object* v_val_3007_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_string_utf8_at_end(v_s_3005_, v_i_3006_);
if (v___x_3008_ == 0)
{
uint32_t v_c_3009_; uint8_t v___y_3011_; uint32_t v___x_3025_; uint8_t v___x_3026_; 
v_c_3009_ = lean_string_utf8_get(v_s_3005_, v_i_3006_);
v___x_3025_ = 48;
v___x_3026_ = lean_uint32_dec_le(v___x_3025_, v_c_3009_);
if (v___x_3026_ == 0)
{
v___y_3011_ = v___x_3026_;
goto v___jp_3010_;
}
else
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 57;
v___x_3028_ = lean_uint32_dec_le(v_c_3009_, v___x_3027_);
v___y_3011_ = v___x_3028_;
goto v___jp_3010_;
}
v___jp_3010_:
{
if (v___y_3011_ == 0)
{
uint32_t v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = 95;
v___x_3013_ = lean_uint32_dec_eq(v_c_3009_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_val_3007_);
lean_dec(v_i_3006_);
v___x_3014_ = lean_box(0);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_string_utf8_next(v_s_3005_, v_i_3006_);
lean_dec(v_i_3006_);
v_i_3006_ = v___x_3015_;
goto _start;
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3017_ = lean_string_utf8_next(v_s_3005_, v_i_3006_);
lean_dec(v_i_3006_);
v___x_3018_ = lean_unsigned_to_nat(10u);
v___x_3019_ = lean_nat_mul(v___x_3018_, v_val_3007_);
lean_dec(v_val_3007_);
v___x_3020_ = lean_uint32_to_nat(v_c_3009_);
v___x_3021_ = lean_nat_add(v___x_3019_, v___x_3020_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_unsigned_to_nat(48u);
v___x_3023_ = lean_nat_sub(v___x_3021_, v___x_3022_);
lean_dec(v___x_3021_);
v_i_3006_ = v___x_3017_;
v_val_3007_ = v___x_3023_;
goto _start;
}
}
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_i_3006_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_val_3007_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3030_, lean_object* v_i_3031_, lean_object* v_val_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3030_, v_i_3031_, v_val_3032_);
lean_dec_ref(v_s_3030_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3036_){
_start:
{
lean_object* v_len_3037_; lean_object* v___x_3038_; uint8_t v___y_3040_; uint8_t v___y_3053_; uint8_t v___x_3056_; 
v_len_3037_ = lean_string_length(v_s_3036_);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3056_ = lean_nat_dec_eq(v_len_3037_, v___x_3038_);
if (v___x_3056_ == 0)
{
uint32_t v_c_3057_; uint32_t v___x_3058_; uint8_t v___x_3059_; 
v_c_3057_ = lean_string_utf8_get(v_s_3036_, v___x_3038_);
v___x_3058_ = 48;
v___x_3059_ = lean_uint32_dec_eq(v_c_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
uint8_t v___x_3060_; 
lean_dec(v_len_3037_);
v___x_3060_ = lean_uint32_dec_le(v___x_3058_, v_c_3057_);
if (v___x_3060_ == 0)
{
v___y_3053_ = v___x_3060_;
goto v___jp_3052_;
}
else
{
uint32_t v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = 57;
v___x_3062_ = lean_uint32_dec_le(v_c_3057_, v___x_3061_);
v___y_3053_ = v___x_3062_;
goto v___jp_3052_;
}
}
else
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_unsigned_to_nat(1u);
v___x_3064_ = lean_nat_dec_eq(v_len_3037_, v___x_3063_);
lean_dec(v_len_3037_);
if (v___x_3064_ == 0)
{
uint32_t v_c_3065_; uint32_t v___x_3066_; uint8_t v___x_3067_; 
v_c_3065_ = lean_string_utf8_get(v_s_3036_, v___x_3063_);
v___x_3066_ = 120;
v___x_3067_ = lean_uint32_dec_eq(v_c_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
uint32_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = 88;
v___x_3069_ = lean_uint32_dec_eq(v_c_3065_, v___x_3068_);
if (v___x_3069_ == 0)
{
uint32_t v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = 98;
v___x_3071_ = lean_uint32_dec_eq(v_c_3065_, v___x_3070_);
if (v___x_3071_ == 0)
{
uint32_t v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = 66;
v___x_3073_ = lean_uint32_dec_eq(v_c_3065_, v___x_3072_);
if (v___x_3073_ == 0)
{
uint32_t v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = 111;
v___x_3075_ = lean_uint32_dec_eq(v_c_3065_, v___x_3074_);
if (v___x_3075_ == 0)
{
uint32_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = 79;
v___x_3077_ = lean_uint32_dec_eq(v_c_3065_, v___x_3076_);
if (v___x_3077_ == 0)
{
uint8_t v___x_3078_; 
v___x_3078_ = lean_uint32_dec_le(v___x_3058_, v_c_3065_);
if (v___x_3078_ == 0)
{
v___y_3040_ = v___x_3078_;
goto v___jp_3039_;
}
else
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 57;
v___x_3080_ = lean_uint32_dec_le(v_c_3065_, v___x_3079_);
v___y_3040_ = v___x_3080_;
goto v___jp_3039_;
}
}
else
{
goto v___jp_3043_;
}
}
else
{
goto v___jp_3043_;
}
}
else
{
goto v___jp_3046_;
}
}
else
{
goto v___jp_3046_;
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
lean_object* v___x_3081_; 
v___x_3081_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3081_;
}
}
}
else
{
lean_object* v___x_3082_; 
lean_dec(v_len_3037_);
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
v___jp_3039_:
{
if (v___y_3040_ == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_box(0);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3036_, v___x_3038_, v___x_3038_);
return v___x_3042_;
}
}
v___jp_3043_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = lean_unsigned_to_nat(2u);
v___x_3045_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3036_, v___x_3044_, v___x_3038_);
return v___x_3045_;
}
v___jp_3046_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_unsigned_to_nat(2u);
v___x_3048_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3036_, v___x_3047_, v___x_3038_);
return v___x_3048_;
}
v___jp_3049_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3036_, v___x_3050_, v___x_3038_);
return v___x_3051_;
}
v___jp_3052_:
{
if (v___y_3053_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_box(0);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3036_, v___x_3038_, v___x_3038_);
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3083_);
lean_dec_ref(v_s_3083_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3085_, lean_object* v_stx_3086_){
_start:
{
if (lean_obj_tag(v_stx_3086_) == 1)
{
lean_object* v_kind_3087_; lean_object* v_args_3088_; uint8_t v___x_3089_; 
v_kind_3087_ = lean_ctor_get(v_stx_3086_, 1);
v_args_3088_ = lean_ctor_get(v_stx_3086_, 2);
v___x_3089_ = lean_name_eq(v_kind_3087_, v_litKind_3085_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_box(0);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = lean_array_get_size(v_args_3088_);
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = lean_nat_dec_eq(v___x_3091_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_box(0);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_array_fget_borrowed(v_args_3088_, v___x_3095_);
if (lean_obj_tag(v___x_3096_) == 2)
{
lean_object* v_val_3097_; lean_object* v___x_3098_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 1);
lean_inc_ref(v_val_3097_);
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_val_3097_);
return v___x_3098_;
}
else
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
}
}
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_box(0);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3101_, lean_object* v_stx_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Syntax_isLit_x3f(v_litKind_3101_, v_stx_3102_);
lean_dec(v_stx_3102_);
lean_dec(v_litKind_3101_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3104_, lean_object* v_stx_3105_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Syntax_isLit_x3f(v_litKind_3104_, v_stx_3105_);
if (lean_obj_tag(v___x_3106_) == 1)
{
lean_object* v_val_3107_; lean_object* v___x_3108_; 
v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3107_);
lean_dec(v_val_3107_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; 
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3110_, lean_object* v_stx_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3110_, v_stx_3111_);
lean_dec(v_stx_3111_);
lean_dec(v_litKind_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3113_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3115_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3114_, v_s_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_Syntax_isNatLit_x3f(v_s_3116_);
lean_dec(v_s_3116_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3123_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3122_, v_s_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3124_);
lean_dec(v_s_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3126_, lean_object* v_i_3127_, lean_object* v_val_3128_, lean_object* v_e_3129_, uint8_t v_sign_3130_, lean_object* v_exp_3131_){
_start:
{
uint8_t v___x_3132_; 
v___x_3132_ = lean_string_utf8_at_end(v_s_3126_, v_i_3127_);
if (v___x_3132_ == 0)
{
uint32_t v_c_3133_; uint8_t v___y_3135_; uint32_t v___x_3149_; uint8_t v___x_3150_; 
v_c_3133_ = lean_string_utf8_get(v_s_3126_, v_i_3127_);
v___x_3149_ = 48;
v___x_3150_ = lean_uint32_dec_le(v___x_3149_, v_c_3133_);
if (v___x_3150_ == 0)
{
v___y_3135_ = v___x_3150_;
goto v___jp_3134_;
}
else
{
uint32_t v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = 57;
v___x_3152_ = lean_uint32_dec_le(v_c_3133_, v___x_3151_);
v___y_3135_ = v___x_3152_;
goto v___jp_3134_;
}
v___jp_3134_:
{
if (v___y_3135_ == 0)
{
uint32_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = 95;
v___x_3137_ = lean_uint32_dec_eq(v_c_3133_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec(v_exp_3131_);
lean_dec(v_val_3128_);
lean_dec(v_i_3127_);
v___x_3138_ = lean_box(0);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_string_utf8_next(v_s_3126_, v_i_3127_);
lean_dec(v_i_3127_);
v_i_3127_ = v___x_3139_;
goto _start;
}
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3141_ = lean_string_utf8_next(v_s_3126_, v_i_3127_);
lean_dec(v_i_3127_);
v___x_3142_ = lean_unsigned_to_nat(10u);
v___x_3143_ = lean_nat_mul(v___x_3142_, v_exp_3131_);
lean_dec(v_exp_3131_);
v___x_3144_ = lean_uint32_to_nat(v_c_3133_);
v___x_3145_ = lean_nat_add(v___x_3143_, v___x_3144_);
lean_dec(v___x_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_unsigned_to_nat(48u);
v___x_3147_ = lean_nat_sub(v___x_3145_, v___x_3146_);
lean_dec(v___x_3145_);
v_i_3127_ = v___x_3141_;
v_exp_3131_ = v___x_3147_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3127_);
if (v_sign_3130_ == 0)
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_le(v_e_3129_, v_exp_3131_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3154_ = lean_nat_sub(v_e_3129_, v_exp_3131_);
lean_dec(v_exp_3131_);
v___x_3155_ = lean_box(v___x_3132_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___x_3154_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_val_3128_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3159_ = lean_nat_sub(v_exp_3131_, v_e_3129_);
lean_dec(v_exp_3131_);
v___x_3160_ = lean_box(v_sign_3130_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v_val_3128_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3164_ = lean_nat_add(v_exp_3131_, v_e_3129_);
lean_dec(v_exp_3131_);
v___x_3165_ = lean_box(v_sign_3130_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
v___x_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3167_, 0, v_val_3128_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3169_, lean_object* v_i_3170_, lean_object* v_val_3171_, lean_object* v_e_3172_, lean_object* v_sign_3173_, lean_object* v_exp_3174_){
_start:
{
uint8_t v_sign_boxed_3175_; lean_object* v_res_3176_; 
v_sign_boxed_3175_ = lean_unbox(v_sign_3173_);
v_res_3176_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3169_, v_i_3170_, v_val_3171_, v_e_3172_, v_sign_boxed_3175_, v_exp_3174_);
lean_dec(v_e_3172_);
lean_dec_ref(v_s_3169_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3177_, lean_object* v_i_3178_, lean_object* v_val_3179_, lean_object* v_e_3180_){
_start:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_string_utf8_at_end(v_s_3177_, v_i_3178_);
if (v___x_3181_ == 0)
{
uint32_t v_c_3182_; uint32_t v___x_3183_; uint8_t v___x_3184_; 
v_c_3182_ = lean_string_utf8_get(v_s_3177_, v_i_3178_);
v___x_3183_ = 45;
v___x_3184_ = lean_uint32_dec_eq(v_c_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 43;
v___x_3186_ = lean_uint32_dec_eq(v_c_3182_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3177_, v_i_3178_, v_val_3179_, v_e_3180_, v___x_3186_, v___x_3187_);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_string_utf8_next(v_s_3177_, v_i_3178_);
lean_dec(v_i_3178_);
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3177_, v___x_3189_, v_val_3179_, v_e_3180_, v___x_3184_, v___x_3190_);
return v___x_3191_;
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_string_utf8_next(v_s_3177_, v_i_3178_);
lean_dec(v_i_3178_);
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3177_, v___x_3192_, v_val_3179_, v_e_3180_, v___x_3184_, v___x_3193_);
return v___x_3194_;
}
}
else
{
lean_object* v___x_3195_; 
lean_dec(v_val_3179_);
lean_dec(v_i_3178_);
v___x_3195_ = lean_box(0);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3196_, lean_object* v_i_3197_, lean_object* v_val_3198_, lean_object* v_e_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3196_, v_i_3197_, v_val_3198_, v_e_3199_);
lean_dec(v_e_3199_);
lean_dec_ref(v_s_3196_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3201_, lean_object* v_i_3202_, lean_object* v_val_3203_, lean_object* v_e_3204_){
_start:
{
uint8_t v___x_3208_; 
v___x_3208_ = lean_string_utf8_at_end(v_s_3201_, v_i_3202_);
if (v___x_3208_ == 0)
{
uint32_t v_c_3209_; uint8_t v___y_3211_; uint32_t v___x_3231_; uint8_t v___x_3232_; 
v_c_3209_ = lean_string_utf8_get(v_s_3201_, v_i_3202_);
v___x_3231_ = 48;
v___x_3232_ = lean_uint32_dec_le(v___x_3231_, v_c_3209_);
if (v___x_3232_ == 0)
{
v___y_3211_ = v___x_3232_;
goto v___jp_3210_;
}
else
{
uint32_t v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = 57;
v___x_3234_ = lean_uint32_dec_le(v_c_3209_, v___x_3233_);
v___y_3211_ = v___x_3234_;
goto v___jp_3210_;
}
v___jp_3210_:
{
if (v___y_3211_ == 0)
{
uint32_t v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = 95;
v___x_3213_ = lean_uint32_dec_eq(v_c_3209_, v___x_3212_);
if (v___x_3213_ == 0)
{
uint32_t v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = 101;
v___x_3215_ = lean_uint32_dec_eq(v_c_3209_, v___x_3214_);
if (v___x_3215_ == 0)
{
uint32_t v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = 69;
v___x_3217_ = lean_uint32_dec_eq(v_c_3209_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec(v_e_3204_);
lean_dec(v_val_3203_);
lean_dec(v_i_3202_);
v___x_3218_ = lean_box(0);
return v___x_3218_;
}
else
{
goto v___jp_3205_;
}
}
else
{
goto v___jp_3205_;
}
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_string_utf8_next(v_s_3201_, v_i_3202_);
lean_dec(v_i_3202_);
v_i_3202_ = v___x_3219_;
goto _start;
}
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3221_ = lean_string_utf8_next(v_s_3201_, v_i_3202_);
lean_dec(v_i_3202_);
v___x_3222_ = lean_unsigned_to_nat(10u);
v___x_3223_ = lean_nat_mul(v___x_3222_, v_val_3203_);
lean_dec(v_val_3203_);
v___x_3224_ = lean_uint32_to_nat(v_c_3209_);
v___x_3225_ = lean_nat_add(v___x_3223_, v___x_3224_);
lean_dec(v___x_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_unsigned_to_nat(48u);
v___x_3227_ = lean_nat_sub(v___x_3225_, v___x_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_add(v_e_3204_, v___x_3228_);
lean_dec(v_e_3204_);
v_i_3202_ = v___x_3221_;
v_val_3203_ = v___x_3227_;
v_e_3204_ = v___x_3229_;
goto _start;
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec(v_i_3202_);
v___x_3235_ = lean_box(v___x_3208_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set(v___x_3236_, 1, v_e_3204_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_val_3203_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
v___jp_3205_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_string_utf8_next(v_s_3201_, v_i_3202_);
lean_dec(v_i_3202_);
v___x_3207_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3201_, v___x_3206_, v_val_3203_, v_e_3204_);
lean_dec(v_e_3204_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3239_, lean_object* v_i_3240_, lean_object* v_val_3241_, lean_object* v_e_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3239_, v_i_3240_, v_val_3241_, v_e_3242_);
lean_dec_ref(v_s_3239_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3244_, lean_object* v_i_3245_, lean_object* v_val_3246_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = lean_string_utf8_at_end(v_s_3244_, v_i_3245_);
if (v___x_3251_ == 0)
{
uint32_t v_c_3252_; uint8_t v___y_3254_; uint32_t v___x_3277_; uint8_t v___x_3278_; 
v_c_3252_ = lean_string_utf8_get(v_s_3244_, v_i_3245_);
v___x_3277_ = 48;
v___x_3278_ = lean_uint32_dec_le(v___x_3277_, v_c_3252_);
if (v___x_3278_ == 0)
{
v___y_3254_ = v___x_3278_;
goto v___jp_3253_;
}
else
{
uint32_t v___x_3279_; uint8_t v___x_3280_; 
v___x_3279_ = 57;
v___x_3280_ = lean_uint32_dec_le(v_c_3252_, v___x_3279_);
v___y_3254_ = v___x_3280_;
goto v___jp_3253_;
}
v___jp_3253_:
{
if (v___y_3254_ == 0)
{
uint32_t v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = 95;
v___x_3256_ = lean_uint32_dec_eq(v_c_3252_, v___x_3255_);
if (v___x_3256_ == 0)
{
uint32_t v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = 46;
v___x_3258_ = lean_uint32_dec_eq(v_c_3252_, v___x_3257_);
if (v___x_3258_ == 0)
{
uint32_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = 101;
v___x_3260_ = lean_uint32_dec_eq(v_c_3252_, v___x_3259_);
if (v___x_3260_ == 0)
{
uint32_t v___x_3261_; uint8_t v___x_3262_; 
v___x_3261_ = 69;
v___x_3262_ = lean_uint32_dec_eq(v_c_3252_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec(v_val_3246_);
lean_dec(v_i_3245_);
v___x_3263_ = lean_box(0);
return v___x_3263_;
}
else
{
goto v___jp_3247_;
}
}
else
{
goto v___jp_3247_;
}
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3244_, v___x_3264_, v_val_3246_, v___x_3265_);
return v___x_3266_;
}
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v_i_3245_ = v___x_3267_;
goto _start;
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3269_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v___x_3270_ = lean_unsigned_to_nat(10u);
v___x_3271_ = lean_nat_mul(v___x_3270_, v_val_3246_);
lean_dec(v_val_3246_);
v___x_3272_ = lean_uint32_to_nat(v_c_3252_);
v___x_3273_ = lean_nat_add(v___x_3271_, v___x_3272_);
lean_dec(v___x_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_unsigned_to_nat(48u);
v___x_3275_ = lean_nat_sub(v___x_3273_, v___x_3274_);
lean_dec(v___x_3273_);
v_i_3245_ = v___x_3269_;
v_val_3246_ = v___x_3275_;
goto _start;
}
}
}
else
{
lean_object* v___x_3281_; 
lean_dec(v_val_3246_);
lean_dec(v_i_3245_);
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
v___jp_3247_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v___x_3249_ = lean_unsigned_to_nat(0u);
v___x_3250_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3244_, v___x_3248_, v_val_3246_, v___x_3249_);
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3282_, lean_object* v_i_3283_, lean_object* v_val_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3282_, v_i_3283_, v_val_3284_);
lean_dec_ref(v_s_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3286_){
_start:
{
lean_object* v_len_3287_; lean_object* v___x_3288_; uint8_t v___y_3290_; uint8_t v___x_3293_; 
v_len_3287_ = lean_string_length(v_s_3286_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_nat_dec_eq(v_len_3287_, v___x_3288_);
lean_dec(v_len_3287_);
if (v___x_3293_ == 0)
{
uint32_t v_c_3294_; uint32_t v___x_3295_; uint8_t v___x_3296_; 
v_c_3294_ = lean_string_utf8_get(v_s_3286_, v___x_3288_);
v___x_3295_ = 48;
v___x_3296_ = lean_uint32_dec_le(v___x_3295_, v_c_3294_);
if (v___x_3296_ == 0)
{
v___y_3290_ = v___x_3296_;
goto v___jp_3289_;
}
else
{
uint32_t v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = 57;
v___x_3298_ = lean_uint32_dec_le(v_c_3294_, v___x_3297_);
v___y_3290_ = v___x_3298_;
goto v___jp_3289_;
}
}
else
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
v___jp_3289_:
{
if (v___y_3290_ == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_box(0);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3286_, v___x_3288_, v___x_3288_);
return v___x_3292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3300_);
lean_dec_ref(v_s_3300_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3304_ = l_Lean_Syntax_isLit_x3f(v___x_3303_, v_stx_3302_);
if (lean_obj_tag(v___x_3304_) == 1)
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3305_);
lean_dec(v_val_3305_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; 
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3308_);
lean_dec(v_stx_3308_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3310_){
_start:
{
switch(lean_obj_tag(v_x_3310_))
{
case 2:
{
lean_object* v_val_3311_; lean_object* v___x_3312_; 
v_val_3311_ = lean_ctor_get(v_x_3310_, 1);
lean_inc_ref(v_val_3311_);
lean_dec_ref_known(v_x_3310_, 2);
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_val_3311_);
return v___x_3312_;
}
case 3:
{
lean_object* v_rawVal_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_rawVal_3313_ = lean_ctor_get(v_x_3310_, 1);
lean_inc_ref(v_rawVal_3313_);
lean_dec_ref_known(v_x_3310_, 4);
v___x_3314_ = lean_substring_tostring(v_rawVal_3313_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
default: 
{
lean_object* v___x_3316_; 
lean_dec(v_x_3310_);
v___x_3316_ = lean_box(0);
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_unsigned_to_nat(0u);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; 
v_val_3320_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v___x_3318_, 1);
return v_val_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Syntax_toNat(v_stx_3321_);
lean_dec(v_stx_3321_);
return v_res_3322_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = 9;
v___x_3324_ = lean_box_uint32(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = 10;
v___x_3326_ = lean_box_uint32(v___x_3325_);
return v___x_3326_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = 13;
v___x_3328_ = lean_box_uint32(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = 39;
v___x_3330_ = lean_box_uint32(v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = 34;
v___x_3332_ = lean_box_uint32(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = 92;
v___x_3334_ = lean_box_uint32(v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3335_, lean_object* v_i_3336_){
_start:
{
uint32_t v_c_3337_; lean_object* v_i_3338_; uint32_t v___x_3339_; uint8_t v___x_3340_; 
v_c_3337_ = lean_string_utf8_get(v_s_3335_, v_i_3336_);
v_i_3338_ = lean_string_utf8_next(v_s_3335_, v_i_3336_);
v___x_3339_ = 92;
v___x_3340_ = lean_uint32_dec_eq(v_c_3337_, v___x_3339_);
if (v___x_3340_ == 0)
{
uint32_t v___x_3341_; uint8_t v___x_3342_; 
v___x_3341_ = 34;
v___x_3342_ = lean_uint32_dec_eq(v_c_3337_, v___x_3341_);
if (v___x_3342_ == 0)
{
uint32_t v___x_3343_; uint8_t v___x_3344_; 
v___x_3343_ = 39;
v___x_3344_ = lean_uint32_dec_eq(v_c_3337_, v___x_3343_);
if (v___x_3344_ == 0)
{
uint32_t v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = 114;
v___x_3346_ = lean_uint32_dec_eq(v_c_3337_, v___x_3345_);
if (v___x_3346_ == 0)
{
uint32_t v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = 110;
v___x_3348_ = lean_uint32_dec_eq(v_c_3337_, v___x_3347_);
if (v___x_3348_ == 0)
{
uint32_t v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = 116;
v___x_3350_ = lean_uint32_dec_eq(v_c_3337_, v___x_3349_);
if (v___x_3350_ == 0)
{
uint32_t v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = 120;
v___x_3352_ = lean_uint32_dec_eq(v_c_3337_, v___x_3351_);
if (v___x_3352_ == 0)
{
uint32_t v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = 117;
v___x_3354_ = lean_uint32_dec_eq(v_c_3337_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v_i_3338_);
v___x_3355_ = lean_box(0);
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; 
v___x_3356_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_i_3338_);
lean_dec(v_i_3338_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_box(0);
return v___x_3357_;
}
else
{
lean_object* v_val_3358_; lean_object* v_fst_3359_; lean_object* v_snd_3360_; lean_object* v___x_3361_; 
v_val_3358_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___x_3356_, 1);
v_fst_3359_ = lean_ctor_get(v_val_3358_, 0);
lean_inc(v_fst_3359_);
v_snd_3360_ = lean_ctor_get(v_val_3358_, 1);
lean_inc(v_snd_3360_);
lean_dec(v_val_3358_);
v___x_3361_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3360_);
lean_dec(v_snd_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
lean_dec(v_fst_3359_);
v___x_3362_ = lean_box(0);
return v___x_3362_;
}
else
{
lean_object* v_val_3363_; lean_object* v_fst_3364_; lean_object* v_snd_3365_; lean_object* v___x_3366_; 
v_val_3363_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3363_);
lean_dec_ref_known(v___x_3361_, 1);
v_fst_3364_ = lean_ctor_get(v_val_3363_, 0);
lean_inc(v_fst_3364_);
v_snd_3365_ = lean_ctor_get(v_val_3363_, 1);
lean_inc(v_snd_3365_);
lean_dec(v_val_3363_);
v___x_3366_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3365_);
lean_dec(v_snd_3365_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec(v_fst_3364_);
lean_dec(v_fst_3359_);
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
v___x_3371_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3370_);
lean_dec(v_snd_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec(v_fst_3369_);
lean_dec(v_fst_3364_);
lean_dec(v_fst_3359_);
v___x_3372_ = lean_box(0);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3398_; 
v_val_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3398_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3398_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3397_; 
v_fst_3377_ = lean_ctor_get(v_val_3373_, 0);
v_snd_3378_ = lean_ctor_get(v_val_3373_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_val_3373_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3380_ = v_val_3373_;
v_isShared_3381_ = v_isSharedCheck_3397_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_val_3373_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3397_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint32_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3382_ = lean_unsigned_to_nat(16u);
v___x_3383_ = lean_nat_mul(v___x_3382_, v_fst_3359_);
lean_dec(v_fst_3359_);
v___x_3384_ = lean_nat_add(v___x_3383_, v_fst_3364_);
lean_dec(v_fst_3364_);
lean_dec(v___x_3383_);
v___x_3385_ = lean_nat_mul(v___x_3382_, v___x_3384_);
lean_dec(v___x_3384_);
v___x_3386_ = lean_nat_add(v___x_3385_, v_fst_3369_);
lean_dec(v_fst_3369_);
lean_dec(v___x_3385_);
v___x_3387_ = lean_nat_mul(v___x_3382_, v___x_3386_);
lean_dec(v___x_3386_);
v___x_3388_ = lean_nat_add(v___x_3387_, v_fst_3377_);
lean_dec(v_fst_3377_);
lean_dec(v___x_3387_);
v___x_3389_ = l_Char_ofNat(v___x_3388_);
lean_dec(v___x_3388_);
v___x_3390_ = lean_box_uint32(v___x_3389_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3390_);
v___x_3392_ = v___x_3380_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_snd_3378_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3392_);
v___x_3394_ = v___x_3375_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
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
lean_object* v___x_3399_; 
v___x_3399_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_i_3338_);
lean_dec(v_i_3338_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_box(0);
return v___x_3400_;
}
else
{
lean_object* v_val_3401_; lean_object* v_fst_3402_; lean_object* v_snd_3403_; lean_object* v___x_3404_; 
v_val_3401_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3399_, 1);
v_fst_3402_ = lean_ctor_get(v_val_3401_, 0);
lean_inc(v_fst_3402_);
v_snd_3403_ = lean_ctor_get(v_val_3401_, 1);
lean_inc(v_snd_3403_);
lean_dec(v_val_3401_);
v___x_3404_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3403_);
lean_dec(v_snd_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v___x_3405_; 
lean_dec(v_fst_3402_);
v___x_3405_ = lean_box(0);
return v___x_3405_;
}
else
{
lean_object* v_val_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3427_; 
v_val_3406_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3408_ = v___x_3404_;
v_isShared_3409_ = v_isSharedCheck_3427_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_val_3406_);
lean_dec(v___x_3404_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3427_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3426_; 
v_fst_3410_ = lean_ctor_get(v_val_3406_, 0);
v_snd_3411_ = lean_ctor_get(v_val_3406_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_val_3406_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3413_ = v_val_3406_;
v_isShared_3414_ = v_isSharedCheck_3426_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3410_);
lean_dec(v_val_3406_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3426_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint32_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3415_ = lean_unsigned_to_nat(16u);
v___x_3416_ = lean_nat_mul(v___x_3415_, v_fst_3402_);
lean_dec(v_fst_3402_);
v___x_3417_ = lean_nat_add(v___x_3416_, v_fst_3410_);
lean_dec(v_fst_3410_);
lean_dec(v___x_3416_);
v___x_3418_ = l_Char_ofNat(v___x_3417_);
lean_dec(v___x_3417_);
v___x_3419_ = lean_box_uint32(v___x_3418_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3419_);
v___x_3421_ = v___x_3413_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_snd_3411_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3423_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3421_);
v___x_3423_ = v___x_3408_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
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
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v_i_3338_);
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v_i_3338_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
return v___x_3433_;
}
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
lean_ctor_set(v___x_3435_, 1, v_i_3338_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v_i_3338_);
v___x_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v_i_3338_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
return v___x_3442_;
}
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v_i_3338_);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3446_, lean_object* v_i_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Syntax_decodeQuotedChar(v_s_3446_, v_i_3447_);
lean_dec(v_i_3447_);
lean_dec_ref(v_s_3446_);
return v_res_3448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3449_){
_start:
{
uint8_t v___y_3451_; uint32_t v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = 32;
v___x_3457_ = lean_uint32_dec_eq(v___y_3449_, v___x_3456_);
if (v___x_3457_ == 0)
{
uint32_t v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = 9;
v___x_3459_ = lean_uint32_dec_eq(v___y_3449_, v___x_3458_);
v___y_3451_ = v___x_3459_;
goto v___jp_3450_;
}
else
{
v___y_3451_ = v___x_3457_;
goto v___jp_3450_;
}
v___jp_3450_:
{
if (v___y_3451_ == 0)
{
uint32_t v___x_3452_; uint8_t v___x_3453_; 
v___x_3452_ = 13;
v___x_3453_ = lean_uint32_dec_eq(v___y_3449_, v___x_3452_);
if (v___x_3453_ == 0)
{
uint32_t v___x_3454_; uint8_t v___x_3455_; 
v___x_3454_ = 10;
v___x_3455_ = lean_uint32_dec_eq(v___y_3449_, v___x_3454_);
return v___x_3455_;
}
else
{
return v___x_3453_;
}
}
else
{
return v___y_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3460_){
_start:
{
uint32_t v___y_233__boxed_3461_; uint8_t v_res_3462_; lean_object* v_r_3463_; 
v___y_233__boxed_3461_ = lean_unbox_uint32(v___y_3460_);
lean_dec(v___y_3460_);
v_res_3462_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_233__boxed_3461_);
v_r_3463_ = lean_box(v_res_3462_);
return v_r_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3465_, lean_object* v_i_3466_){
_start:
{
lean_object* v___f_3467_; uint8_t v___y_3473_; uint32_t v___x_3475_; uint8_t v___y_3477_; uint32_t v___x_3482_; uint8_t v___x_3483_; 
v___f_3467_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3475_ = lean_string_utf8_get(v_s_3465_, v_i_3466_);
v___x_3482_ = 32;
v___x_3483_ = lean_uint32_dec_eq(v___x_3475_, v___x_3482_);
if (v___x_3483_ == 0)
{
uint32_t v___x_3484_; uint8_t v___x_3485_; 
v___x_3484_ = 9;
v___x_3485_ = lean_uint32_dec_eq(v___x_3475_, v___x_3484_);
v___y_3477_ = v___x_3485_;
goto v___jp_3476_;
}
else
{
v___y_3477_ = v___x_3483_;
goto v___jp_3476_;
}
v___jp_3468_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_string_utf8_next(v_s_3465_, v_i_3466_);
v___x_3470_ = lean_string_nextwhile(v_s_3465_, v___f_3467_, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
v___jp_3472_:
{
if (v___y_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref(v_s_3465_);
v___x_3474_ = lean_box(0);
return v___x_3474_;
}
else
{
goto v___jp_3468_;
}
}
v___jp_3476_:
{
if (v___y_3477_ == 0)
{
uint32_t v___x_3478_; uint8_t v___x_3479_; 
v___x_3478_ = 13;
v___x_3479_ = lean_uint32_dec_eq(v___x_3475_, v___x_3478_);
if (v___x_3479_ == 0)
{
uint32_t v___x_3480_; uint8_t v___x_3481_; 
v___x_3480_ = 10;
v___x_3481_ = lean_uint32_dec_eq(v___x_3475_, v___x_3480_);
v___y_3473_ = v___x_3481_;
goto v___jp_3472_;
}
else
{
v___y_3473_ = v___x_3479_;
goto v___jp_3472_;
}
}
else
{
goto v___jp_3468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3486_, lean_object* v_i_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Syntax_decodeStringGap(v_s_3486_, v_i_3487_);
lean_dec(v_i_3487_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3489_, lean_object* v_i_3490_, lean_object* v_acc_3491_){
_start:
{
uint32_t v_c_3492_; uint32_t v___x_3493_; uint8_t v___x_3494_; 
v_c_3492_ = lean_string_utf8_get(v_s_3489_, v_i_3490_);
v___x_3493_ = 34;
v___x_3494_ = lean_uint32_dec_eq(v_c_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v_i_3495_; uint8_t v___x_3496_; 
v_i_3495_ = lean_string_utf8_next(v_s_3489_, v_i_3490_);
lean_dec(v_i_3490_);
v___x_3496_ = lean_string_utf8_at_end(v_s_3489_, v_i_3495_);
if (v___x_3496_ == 0)
{
uint32_t v___x_3497_; uint8_t v___x_3498_; 
v___x_3497_ = 92;
v___x_3498_ = lean_uint32_dec_eq(v_c_3492_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_string_push(v_acc_3491_, v_c_3492_);
v_i_3490_ = v_i_3495_;
v_acc_3491_ = v___x_3499_;
goto _start;
}
else
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Syntax_decodeQuotedChar(v_s_3489_, v_i_3495_);
if (lean_obj_tag(v___x_3501_) == 1)
{
lean_object* v_val_3502_; lean_object* v_fst_3503_; lean_object* v_snd_3504_; uint32_t v___x_3505_; lean_object* v___x_3506_; 
lean_dec(v_i_3495_);
v_val_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_val_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v_fst_3503_ = lean_ctor_get(v_val_3502_, 0);
lean_inc(v_fst_3503_);
v_snd_3504_ = lean_ctor_get(v_val_3502_, 1);
lean_inc(v_snd_3504_);
lean_dec(v_val_3502_);
v___x_3505_ = lean_unbox_uint32(v_fst_3503_);
lean_dec(v_fst_3503_);
v___x_3506_ = lean_string_push(v_acc_3491_, v___x_3505_);
v_i_3490_ = v_snd_3504_;
v_acc_3491_ = v___x_3506_;
goto _start;
}
else
{
lean_object* v___x_3508_; 
lean_dec(v___x_3501_);
lean_inc_ref(v_s_3489_);
v___x_3508_ = l_Lean_Syntax_decodeStringGap(v_s_3489_, v_i_3495_);
lean_dec(v_i_3495_);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_val_3509_; 
v_val_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v_i_3490_ = v_val_3509_;
goto _start;
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3508_);
lean_dec_ref(v_acc_3491_);
lean_dec_ref(v_s_3489_);
v___x_3511_ = lean_box(0);
return v___x_3511_;
}
}
}
}
else
{
lean_object* v___x_3512_; 
lean_dec(v_i_3495_);
lean_dec_ref(v_acc_3491_);
lean_dec_ref(v_s_3489_);
v___x_3512_ = lean_box(0);
return v___x_3512_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_i_3490_);
lean_dec_ref(v_s_3489_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_acc_3491_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3514_, lean_object* v_i_3515_, lean_object* v_num_3516_){
_start:
{
uint32_t v_c_3517_; lean_object* v_i_3518_; uint32_t v___x_3519_; uint8_t v___x_3520_; 
v_c_3517_ = lean_string_utf8_get(v_s_3514_, v_i_3515_);
v_i_3518_ = lean_string_utf8_next(v_s_3514_, v_i_3515_);
lean_dec(v_i_3515_);
v___x_3519_ = 35;
v___x_3520_ = lean_uint32_dec_eq(v_c_3517_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3521_ = lean_string_utf8_byte_size(v_s_3514_);
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = lean_nat_add(v_num_3516_, v___x_3522_);
lean_dec(v_num_3516_);
v___x_3524_ = lean_nat_sub(v___x_3521_, v___x_3523_);
lean_dec(v___x_3523_);
v___x_3525_ = lean_string_utf8_extract(v_s_3514_, v_i_3518_, v___x_3524_);
lean_dec(v___x_3524_);
lean_dec(v_i_3518_);
return v___x_3525_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_nat_add(v_num_3516_, v___x_3526_);
lean_dec(v_num_3516_);
v_i_3515_ = v_i_3518_;
v_num_3516_ = v___x_3527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3529_, lean_object* v_i_3530_, lean_object* v_num_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3529_, v_i_3530_, v_num_3531_);
lean_dec_ref(v_s_3529_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3533_){
_start:
{
lean_object* v___x_3534_; uint32_t v___x_3535_; uint32_t v___x_3536_; uint8_t v___x_3537_; 
v___x_3534_ = lean_unsigned_to_nat(0u);
v___x_3535_ = lean_string_utf8_get(v_s_3533_, v___x_3534_);
v___x_3536_ = 114;
v___x_3537_ = lean_uint32_dec_eq(v___x_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = lean_unsigned_to_nat(1u);
v___x_3539_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3540_ = l_Lean_Syntax_decodeStrLitAux(v_s_3533_, v___x_3538_, v___x_3539_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3533_, v___x_3541_, v___x_3534_);
lean_dec_ref(v_s_3533_);
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3544_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3546_ = l_Lean_Syntax_isLit_x3f(v___x_3545_, v_stx_3544_);
if (lean_obj_tag(v___x_3546_) == 1)
{
lean_object* v_val_3547_; lean_object* v___x_3548_; 
v_val_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_val_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = l_Lean_Syntax_decodeStrLit(v_val_3547_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3550_);
lean_dec(v_stx_3550_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3552_){
_start:
{
lean_object* v___x_3553_; uint32_t v_c_3554_; uint32_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3553_ = lean_unsigned_to_nat(1u);
v_c_3554_ = lean_string_utf8_get(v_s_3552_, v___x_3553_);
v___x_3555_ = 92;
v___x_3556_ = lean_uint32_dec_eq(v_c_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_box_uint32(v_c_3554_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_unsigned_to_nat(2u);
v___x_3560_ = l_Lean_Syntax_decodeQuotedChar(v_s_3552_, v___x_3559_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_box(0);
return v___x_3561_;
}
else
{
lean_object* v_val_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3570_; 
v_val_3562_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3564_ = v___x_3560_;
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_val_3562_);
lean_dec(v___x_3560_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_fst_3566_; lean_object* v___x_3568_; 
v_fst_3566_ = lean_ctor_get(v_val_3562_, 0);
lean_inc(v_fst_3566_);
lean_dec(v_val_3562_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v_fst_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_fst_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Syntax_decodeCharLit(v_s_3571_);
lean_dec_ref(v_s_3571_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3575_ = l_Lean_Syntax_isLit_x3f(v___x_3574_, v_stx_3573_);
if (lean_obj_tag(v___x_3575_) == 1)
{
lean_object* v_val_3576_; lean_object* v___x_3577_; 
v_val_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = l_Lean_Syntax_decodeCharLit(v_val_3576_);
lean_dec(v_val_3576_);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; 
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
return v___x_3578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3579_);
lean_dec(v_stx_3579_);
return v_res_3580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3581_){
_start:
{
uint8_t v___y_3583_; uint8_t v___y_3595_; uint32_t v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = 65;
v___x_3606_ = lean_uint32_dec_le(v___x_3605_, v___y_3581_);
if (v___x_3606_ == 0)
{
goto v___jp_3600_;
}
else
{
uint32_t v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = 90;
v___x_3608_ = lean_uint32_dec_le(v___y_3581_, v___x_3607_);
if (v___x_3608_ == 0)
{
goto v___jp_3600_;
}
else
{
return v___x_3608_;
}
}
v___jp_3582_:
{
if (v___y_3583_ == 0)
{
uint32_t v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = 95;
v___x_3585_ = lean_uint32_dec_eq(v___y_3581_, v___x_3584_);
if (v___x_3585_ == 0)
{
uint32_t v___x_3586_; uint8_t v___x_3587_; 
v___x_3586_ = 39;
v___x_3587_ = lean_uint32_dec_eq(v___y_3581_, v___x_3586_);
if (v___x_3587_ == 0)
{
uint32_t v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = 33;
v___x_3589_ = lean_uint32_dec_eq(v___y_3581_, v___x_3588_);
if (v___x_3589_ == 0)
{
uint32_t v___x_3590_; uint8_t v___x_3591_; 
v___x_3590_ = 63;
v___x_3591_ = lean_uint32_dec_eq(v___y_3581_, v___x_3590_);
if (v___x_3591_ == 0)
{
uint8_t v___x_3592_; 
v___x_3592_ = l_Lean_isLetterLike(v___y_3581_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = l_Lean_isSubScriptAlnum(v___y_3581_);
return v___x_3593_;
}
else
{
return v___x_3592_;
}
}
else
{
return v___x_3591_;
}
}
else
{
return v___x_3589_;
}
}
else
{
return v___x_3587_;
}
}
else
{
return v___x_3585_;
}
}
else
{
return v___y_3583_;
}
}
v___jp_3594_:
{
if (v___y_3595_ == 0)
{
uint32_t v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = 48;
v___x_3597_ = lean_uint32_dec_le(v___x_3596_, v___y_3581_);
if (v___x_3597_ == 0)
{
v___y_3583_ = v___x_3597_;
goto v___jp_3582_;
}
else
{
uint32_t v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = 57;
v___x_3599_ = lean_uint32_dec_le(v___y_3581_, v___x_3598_);
v___y_3583_ = v___x_3599_;
goto v___jp_3582_;
}
}
else
{
return v___y_3595_;
}
}
v___jp_3600_:
{
uint32_t v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = 97;
v___x_3602_ = lean_uint32_dec_le(v___x_3601_, v___y_3581_);
if (v___x_3602_ == 0)
{
v___y_3595_ = v___x_3602_;
goto v___jp_3594_;
}
else
{
uint32_t v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = 122;
v___x_3604_ = lean_uint32_dec_le(v___y_3581_, v___x_3603_);
v___y_3595_ = v___x_3604_;
goto v___jp_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3609_){
_start:
{
uint32_t v___y_1135__boxed_3610_; uint8_t v_res_3611_; lean_object* v_r_3612_; 
v___y_1135__boxed_3610_ = lean_unbox_uint32(v___y_3609_);
lean_dec(v___y_3609_);
v_res_3611_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_1135__boxed_3610_);
v_r_3612_ = lean_box(v_res_3611_);
return v_r_3612_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___y_3613_){
_start:
{
uint32_t v___x_3614_; uint8_t v___x_3615_; 
v___x_3614_ = 48;
v___x_3615_ = lean_uint32_dec_le(v___x_3614_, v___y_3613_);
if (v___x_3615_ == 0)
{
return v___x_3615_;
}
else
{
uint32_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = 57;
v___x_3617_ = lean_uint32_dec_le(v___y_3613_, v___x_3616_);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___y_3618_){
_start:
{
uint32_t v___y_1192__boxed_3619_; uint8_t v_res_3620_; lean_object* v_r_3621_; 
v___y_1192__boxed_3619_ = lean_unbox_uint32(v___y_3618_);
lean_dec(v___y_3618_);
v_res_3620_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___y_1192__boxed_3619_);
v_r_3621_ = lean_box(v_res_3620_);
return v_r_3621_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3622_, uint8_t v___x_3623_, uint32_t v_x_3624_){
_start:
{
uint32_t v___x_3625_; uint8_t v___x_3626_; 
v___x_3625_ = 187;
v___x_3626_ = lean_uint32_dec_eq(v_x_3624_, v___x_3625_);
if (v___x_3626_ == 0)
{
return v___x_3622_;
}
else
{
return v___x_3623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3627_, lean_object* v___x_3628_, lean_object* v_x_3629_){
_start:
{
uint8_t v___x_1203__boxed_3630_; uint8_t v___x_1204__boxed_3631_; uint32_t v_x_1205__boxed_3632_; uint8_t v_res_3633_; lean_object* v_r_3634_; 
v___x_1203__boxed_3630_ = lean_unbox(v___x_3627_);
v___x_1204__boxed_3631_ = lean_unbox(v___x_3628_);
v_x_1205__boxed_3632_ = lean_unbox_uint32(v_x_3629_);
lean_dec(v_x_3629_);
v_res_3633_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_1203__boxed_3630_, v___x_1204__boxed_3631_, v_x_1205__boxed_3632_);
v_r_3634_ = lean_box(v_res_3633_);
return v_r_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3637_, lean_object* v_acc_3638_){
_start:
{
lean_object* v_ss_3640_; lean_object* v_acc_3641_; uint8_t v___x_3650_; 
lean_inc_ref(v_ss_3637_);
v___x_3650_ = lean_substring_isempty(v_ss_3637_);
if (v___x_3650_ == 0)
{
uint32_t v_curr_3651_; uint32_t v___x_3652_; uint8_t v___x_3653_; 
lean_inc_ref(v_ss_3637_);
v_curr_3651_ = lean_substring_front(v_ss_3637_);
v___x_3652_ = 171;
v___x_3653_ = lean_uint32_dec_eq(v_curr_3651_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___f_3654_; lean_object* v___f_3665_; uint8_t v___y_3667_; uint8_t v___y_3679_; uint8_t v___y_3685_; uint32_t v___x_3694_; uint8_t v___x_3695_; 
v___f_3654_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___f_3665_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1));
v___x_3694_ = 65;
v___x_3695_ = lean_uint32_dec_le(v___x_3694_, v_curr_3651_);
if (v___x_3695_ == 0)
{
goto v___jp_3689_;
}
else
{
uint32_t v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = 90;
v___x_3697_ = lean_uint32_dec_le(v_curr_3651_, v___x_3696_);
if (v___x_3697_ == 0)
{
goto v___jp_3689_;
}
else
{
goto v___jp_3655_;
}
}
v___jp_3655_:
{
lean_object* v_idPart_3656_; lean_object* v_startPos_3657_; lean_object* v_stopPos_3658_; lean_object* v_startPos_3659_; lean_object* v_stopPos_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_inc_ref(v_ss_3637_);
v_idPart_3656_ = lean_substring_takewhile(v_ss_3637_, v___f_3654_);
v_startPos_3657_ = lean_ctor_get(v_idPart_3656_, 1);
lean_inc(v_startPos_3657_);
v_stopPos_3658_ = lean_ctor_get(v_idPart_3656_, 2);
lean_inc(v_stopPos_3658_);
v_startPos_3659_ = lean_ctor_get(v_ss_3637_, 1);
v_stopPos_3660_ = lean_ctor_get(v_ss_3637_, 2);
v___x_3661_ = lean_nat_sub(v_stopPos_3658_, v_startPos_3657_);
lean_dec(v_startPos_3657_);
lean_dec(v_stopPos_3658_);
v___x_3662_ = lean_nat_sub(v_stopPos_3660_, v_startPos_3659_);
v___x_3663_ = lean_substring_extract(v_ss_3637_, v___x_3661_, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_idPart_3656_);
lean_ctor_set(v___x_3664_, 1, v_acc_3638_);
v_ss_3640_ = v___x_3663_;
v_acc_3641_ = v___x_3664_;
goto v___jp_3639_;
}
v___jp_3666_:
{
if (v___y_3667_ == 0)
{
lean_object* v___x_3668_; 
lean_dec(v_acc_3638_);
lean_dec_ref(v_ss_3637_);
v___x_3668_ = lean_box(0);
return v___x_3668_;
}
else
{
lean_object* v_idPart_3669_; lean_object* v_startPos_3670_; lean_object* v_stopPos_3671_; lean_object* v_startPos_3672_; lean_object* v_stopPos_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
lean_inc_ref(v_ss_3637_);
v_idPart_3669_ = lean_substring_takewhile(v_ss_3637_, v___f_3665_);
v_startPos_3670_ = lean_ctor_get(v_idPart_3669_, 1);
lean_inc(v_startPos_3670_);
v_stopPos_3671_ = lean_ctor_get(v_idPart_3669_, 2);
lean_inc(v_stopPos_3671_);
v_startPos_3672_ = lean_ctor_get(v_ss_3637_, 1);
v_stopPos_3673_ = lean_ctor_get(v_ss_3637_, 2);
v___x_3674_ = lean_nat_sub(v_stopPos_3671_, v_startPos_3670_);
lean_dec(v_startPos_3670_);
lean_dec(v_stopPos_3671_);
v___x_3675_ = lean_nat_sub(v_stopPos_3673_, v_startPos_3672_);
v___x_3676_ = lean_substring_extract(v_ss_3637_, v___x_3674_, v___x_3675_);
v___x_3677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3677_, 0, v_idPart_3669_);
lean_ctor_set(v___x_3677_, 1, v_acc_3638_);
v_ss_3640_ = v___x_3676_;
v_acc_3641_ = v___x_3677_;
goto v___jp_3639_;
}
}
v___jp_3678_:
{
if (v___y_3679_ == 0)
{
uint32_t v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = 48;
v___x_3681_ = lean_uint32_dec_le(v___x_3680_, v_curr_3651_);
if (v___x_3681_ == 0)
{
v___y_3667_ = v___x_3681_;
goto v___jp_3666_;
}
else
{
uint32_t v___x_3682_; uint8_t v___x_3683_; 
v___x_3682_ = 57;
v___x_3683_ = lean_uint32_dec_le(v_curr_3651_, v___x_3682_);
v___y_3667_ = v___x_3683_;
goto v___jp_3666_;
}
}
else
{
goto v___jp_3655_;
}
}
v___jp_3684_:
{
if (v___y_3685_ == 0)
{
uint32_t v___x_3686_; uint8_t v___x_3687_; 
v___x_3686_ = 95;
v___x_3687_ = lean_uint32_dec_eq(v_curr_3651_, v___x_3686_);
if (v___x_3687_ == 0)
{
uint8_t v___x_3688_; 
v___x_3688_ = l_Lean_isLetterLike(v_curr_3651_);
v___y_3679_ = v___x_3688_;
goto v___jp_3678_;
}
else
{
v___y_3679_ = v___x_3687_;
goto v___jp_3678_;
}
}
else
{
goto v___jp_3655_;
}
}
v___jp_3689_:
{
uint32_t v___x_3690_; uint8_t v___x_3691_; 
v___x_3690_ = 97;
v___x_3691_ = lean_uint32_dec_le(v___x_3690_, v_curr_3651_);
if (v___x_3691_ == 0)
{
v___y_3685_ = v___x_3691_;
goto v___jp_3684_;
}
else
{
uint32_t v___x_3692_; uint8_t v___x_3693_; 
v___x_3692_ = 122;
v___x_3693_ = lean_uint32_dec_le(v_curr_3651_, v___x_3692_);
v___y_3685_ = v___x_3693_;
goto v___jp_3684_;
}
}
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___f_3700_; lean_object* v_escapedPart_3701_; lean_object* v_str_3702_; lean_object* v_startPos_3703_; lean_object* v_stopPos_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3726_; 
v___x_3698_ = lean_box(v___x_3653_);
v___x_3699_ = lean_box(v___x_3650_);
v___f_3700_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3700_, 0, v___x_3698_);
lean_closure_set(v___f_3700_, 1, v___x_3699_);
lean_inc_ref(v_ss_3637_);
v_escapedPart_3701_ = lean_substring_takewhile(v_ss_3637_, v___f_3700_);
v_str_3702_ = lean_ctor_get(v_escapedPart_3701_, 0);
v_startPos_3703_ = lean_ctor_get(v_escapedPart_3701_, 1);
v_stopPos_3704_ = lean_ctor_get(v_escapedPart_3701_, 2);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_escapedPart_3701_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3706_ = v_escapedPart_3701_;
v_isShared_3707_ = v_isSharedCheck_3726_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_stopPos_3704_);
lean_inc(v_startPos_3703_);
lean_inc(v_str_3702_);
lean_dec(v_escapedPart_3701_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3726_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v_startPos_3708_; lean_object* v_stopPos_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v_escapedPart_3713_; 
v_startPos_3708_ = lean_ctor_get(v_ss_3637_, 1);
v_stopPos_3709_ = lean_ctor_get(v_ss_3637_, 2);
v___x_3710_ = lean_string_utf8_next(v_str_3702_, v_stopPos_3704_);
lean_dec(v_stopPos_3704_);
lean_inc(v_stopPos_3709_);
v___x_3711_ = lean_string_pos_min(v_stopPos_3709_, v___x_3710_);
lean_inc(v___x_3711_);
lean_inc(v_startPos_3703_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 2, v___x_3711_);
v_escapedPart_3713_ = v___x_3706_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_str_3702_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_startPos_3703_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v___x_3711_);
v_escapedPart_3713_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3714_; uint8_t v___y_3716_; lean_object* v___x_3721_; uint32_t v___x_3722_; uint32_t v___x_3723_; uint8_t v___x_3724_; 
v___x_3714_ = lean_nat_sub(v___x_3711_, v_startPos_3703_);
lean_dec(v_startPos_3703_);
lean_dec(v___x_3711_);
lean_inc(v___x_3714_);
lean_inc_ref_n(v_escapedPart_3713_, 2);
v___x_3721_ = lean_substring_prev(v_escapedPart_3713_, v___x_3714_);
v___x_3722_ = lean_substring_get(v_escapedPart_3713_, v___x_3721_);
v___x_3723_ = 187;
v___x_3724_ = lean_uint32_dec_eq(v___x_3722_, v___x_3723_);
if (v___x_3724_ == 0)
{
v___y_3716_ = v___x_3653_;
goto v___jp_3715_;
}
else
{
v___y_3716_ = v___x_3650_;
goto v___jp_3715_;
}
v___jp_3715_:
{
if (v___y_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_nat_sub(v_stopPos_3709_, v_startPos_3708_);
v___x_3718_ = lean_substring_extract(v_ss_3637_, v___x_3714_, v___x_3717_);
v___x_3719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3719_, 0, v_escapedPart_3713_);
lean_ctor_set(v___x_3719_, 1, v_acc_3638_);
v_ss_3640_ = v___x_3718_;
v_acc_3641_ = v___x_3719_;
goto v___jp_3639_;
}
else
{
lean_object* v___x_3720_; 
lean_dec(v___x_3714_);
lean_dec_ref(v_escapedPart_3713_);
lean_dec(v_acc_3638_);
lean_dec_ref(v_ss_3637_);
v___x_3720_ = lean_box(0);
return v___x_3720_;
}
}
}
}
}
}
else
{
lean_object* v___x_3727_; 
lean_dec(v_acc_3638_);
lean_dec_ref(v_ss_3637_);
v___x_3727_ = lean_box(0);
return v___x_3727_;
}
v___jp_3639_:
{
uint32_t v___x_3642_; uint32_t v___x_3643_; uint8_t v___x_3644_; 
lean_inc_ref(v_ss_3640_);
v___x_3642_ = lean_substring_front(v_ss_3640_);
v___x_3643_ = 46;
v___x_3644_ = lean_uint32_dec_eq(v___x_3642_, v___x_3643_);
if (v___x_3644_ == 0)
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_substring_isempty(v_ss_3640_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; 
lean_dec(v_acc_3641_);
v___x_3646_ = lean_box(0);
return v___x_3646_;
}
else
{
return v_acc_3641_;
}
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(1u);
v___x_3648_ = lean_substring_drop(v_ss_3640_, v___x_3647_);
v_ss_3637_ = v___x_3648_;
v_acc_3638_ = v_acc_3641_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3728_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = lean_box(0);
v___x_3730_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3728_, v___x_3729_);
v___x_3731_ = l_List_reverse___redArg(v___x_3730_);
return v___x_3731_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3735_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3736_ = lean_unsigned_to_nat(10u);
v___x_3737_ = lean_unsigned_to_nat(1240u);
v___x_3738_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3739_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3740_ = l_mkPanicMessageWithDecl(v___x_3739_, v___x_3738_, v___x_3737_, v___x_3736_, v___x_3735_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3741_, lean_object* v_x_3742_){
_start:
{
if (lean_obj_tag(v_x_3742_) == 0)
{
lean_inc(v_init_3741_);
return v_init_3741_;
}
else
{
lean_object* v_head_3743_; lean_object* v_tail_3744_; lean_object* v___x_3745_; lean_object* v_comp_3746_; uint8_t v___y_3748_; uint32_t v___x_3755_; uint32_t v___x_3756_; uint8_t v___x_3757_; 
v_head_3743_ = lean_ctor_get(v_x_3742_, 0);
lean_inc(v_head_3743_);
v_tail_3744_ = lean_ctor_get(v_x_3742_, 1);
lean_inc(v_tail_3744_);
lean_dec_ref_known(v_x_3742_, 2);
v___x_3745_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3741_, v_tail_3744_);
v_comp_3746_ = lean_substring_tostring(v_head_3743_);
lean_inc_ref(v_comp_3746_);
v___x_3755_ = lean_string_front(v_comp_3746_);
v___x_3756_ = 171;
v___x_3757_ = lean_uint32_dec_eq(v___x_3755_, v___x_3756_);
if (v___x_3757_ == 0)
{
uint32_t v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = 48;
v___x_3759_ = lean_uint32_dec_le(v___x_3758_, v___x_3755_);
if (v___x_3759_ == 0)
{
v___y_3748_ = v___x_3759_;
goto v___jp_3747_;
}
else
{
uint32_t v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = 57;
v___x_3761_ = lean_uint32_dec_le(v___x_3755_, v___x_3760_);
v___y_3748_ = v___x_3761_;
goto v___jp_3747_;
}
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3762_ = lean_unsigned_to_nat(1u);
v___x_3763_ = lean_string_drop(v_comp_3746_, v___x_3762_);
v___x_3764_ = lean_string_dropright(v___x_3763_, v___x_3762_);
v___x_3765_ = l_Lean_Name_str___override(v___x_3745_, v___x_3764_);
return v___x_3765_;
}
v___jp_3747_:
{
if (v___y_3748_ == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Name_str___override(v___x_3745_, v_comp_3746_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3746_);
lean_dec_ref(v_comp_3746_);
if (lean_obj_tag(v___x_3750_) == 1)
{
lean_object* v_val_3751_; lean_object* v___x_3752_; 
v_val_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_val_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v___x_3752_ = l_Lean_Name_num___override(v___x_3745_, v_val_3751_);
return v___x_3752_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec(v___x_3750_);
lean_dec(v___x_3745_);
v___x_3753_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3754_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3753_);
return v___x_3754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3766_, lean_object* v_x_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3766_, v_x_3767_);
lean_dec(v_init_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3769_){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_box(0);
v___x_3771_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3769_, v___x_3770_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_box(0);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_box(0);
v___x_3774_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3773_, v___x_3771_);
return v___x_3774_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3775_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = lean_string_utf8_byte_size(v_s_3775_);
v___x_3778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3778_, 0, v_s_3775_);
lean_ctor_set(v___x_3778_, 1, v___x_3776_);
lean_ctor_set(v___x_3778_, 2, v___x_3777_);
v___x_3779_ = l_Substring_Raw_toName(v___x_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3780_){
_start:
{
lean_object* v___x_3781_; uint32_t v___x_3782_; uint32_t v___x_3783_; uint8_t v___x_3784_; 
v___x_3781_ = lean_unsigned_to_nat(0u);
v___x_3782_ = lean_string_utf8_get(v_s_3780_, v___x_3781_);
v___x_3783_ = 96;
v___x_3784_ = lean_uint32_dec_eq(v___x_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref(v_s_3780_);
v___x_3785_ = lean_box(0);
return v___x_3785_;
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3786_ = lean_string_utf8_byte_size(v_s_3780_);
v___x_3787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3787_, 0, v_s_3780_);
lean_ctor_set(v___x_3787_, 1, v___x_3781_);
lean_ctor_set(v___x_3787_, 2, v___x_3786_);
v___x_3788_ = lean_unsigned_to_nat(1u);
v___x_3789_ = lean_substring_drop(v___x_3787_, v___x_3788_);
v___x_3790_ = l_Substring_Raw_toName(v___x_3789_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_box(0);
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
return v___x_3792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3793_){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3795_ = l_Lean_Syntax_isLit_x3f(v___x_3794_, v_stx_3793_);
if (lean_obj_tag(v___x_3795_) == 1)
{
lean_object* v_val_3796_; lean_object* v___x_3797_; 
v_val_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_val_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___x_3797_ = l_Lean_Syntax_decodeNameLit(v_val_3796_);
return v___x_3797_;
}
else
{
lean_object* v___x_3798_; 
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
return v___x_3798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3799_);
lean_dec(v_stx_3799_);
return v_res_3800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3801_){
_start:
{
if (lean_obj_tag(v_x_3801_) == 1)
{
lean_object* v_args_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
v_args_3802_ = lean_ctor_get(v_x_3801_, 2);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_array_get_size(v_args_3802_);
v___x_3805_ = lean_nat_dec_lt(v___x_3803_, v___x_3804_);
return v___x_3805_;
}
else
{
uint8_t v___x_3806_; 
v___x_3806_ = 0;
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3807_){
_start:
{
uint8_t v_res_3808_; lean_object* v_r_3809_; 
v_res_3808_ = l_Lean_Syntax_hasArgs(v_x_3807_);
lean_dec(v_x_3807_);
v_r_3809_ = lean_box(v_res_3808_);
return v_r_3809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3810_){
_start:
{
if (lean_obj_tag(v_x_3810_) == 2)
{
uint8_t v___x_3811_; 
v___x_3811_ = 1;
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
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3813_){
_start:
{
uint8_t v_res_3814_; lean_object* v_r_3815_; 
v_res_3814_ = l_Lean_Syntax_isAtom(v_x_3813_);
lean_dec(v_x_3813_);
v_r_3815_ = lean_box(v_res_3814_);
return v_r_3815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3816_, lean_object* v_x_3817_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 2)
{
lean_object* v_val_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_val_3818_ = lean_ctor_get(v_x_3817_, 1);
lean_inc_ref(v_val_3818_);
lean_dec_ref_known(v_x_3817_, 2);
v___x_3819_ = lean_string_trim(v_val_3818_);
v___x_3820_ = lean_string_trim(v_token_3816_);
v___x_3821_ = lean_string_dec_eq(v___x_3819_, v___x_3820_);
lean_dec_ref(v___x_3820_);
lean_dec_ref(v___x_3819_);
return v___x_3821_;
}
else
{
uint8_t v___x_3822_; 
lean_dec(v_x_3817_);
lean_dec_ref(v_token_3816_);
v___x_3822_ = 0;
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3823_, lean_object* v_x_3824_){
_start:
{
uint8_t v_res_3825_; lean_object* v_r_3826_; 
v_res_3825_ = l_Lean_Syntax_isToken(v_token_3823_, v_x_3824_);
v_r_3826_ = lean_box(v_res_3825_);
return v_r_3826_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3827_){
_start:
{
switch(lean_obj_tag(v_stx_3827_))
{
case 1:
{
lean_object* v_kind_3828_; lean_object* v_args_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v_kind_3828_ = lean_ctor_get(v_stx_3827_, 1);
v_args_3829_ = lean_ctor_get(v_stx_3827_, 2);
v___x_3830_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3831_ = lean_name_eq(v_kind_3828_, v___x_3830_);
if (v___x_3831_ == 0)
{
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v___x_3832_ = lean_array_get_size(v_args_3829_);
v___x_3833_ = lean_unsigned_to_nat(0u);
v___x_3834_ = lean_nat_dec_eq(v___x_3832_, v___x_3833_);
return v___x_3834_;
}
}
case 0:
{
uint8_t v___x_3835_; 
v___x_3835_ = 1;
return v___x_3835_;
}
default: 
{
uint8_t v___x_3836_; 
v___x_3836_ = 0;
return v___x_3836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3837_){
_start:
{
uint8_t v_res_3838_; lean_object* v_r_3839_; 
v_res_3838_ = l_Lean_Syntax_isNone(v_stx_3837_);
lean_dec(v_stx_3837_);
v_r_3839_ = lean_box(v_res_3838_);
return v_r_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_Syntax_getOptional_x3f(v_stx_3840_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_box(0);
return v___x_3842_;
}
else
{
lean_object* v_val_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3851_; 
v_val_3843_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3845_ = v___x_3841_;
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_val_3843_);
lean_dec(v___x_3841_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = l_Lean_Syntax_getId(v_val_3843_);
lean_dec(v_val_3843_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3847_);
v___x_3849_ = v___x_3845_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3852_);
lean_dec(v_stx_3852_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3854_, lean_object* v_x_3855_){
_start:
{
if (lean_obj_tag(v_x_3855_) == 1)
{
lean_object* v_args_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_args_3856_ = lean_ctor_get(v_x_3855_, 2);
lean_inc_ref(v_p_3854_);
lean_inc_ref(v_x_3855_);
v___x_3857_ = lean_apply_1(v_p_3854_, v_x_3855_);
v___x_3858_ = lean_unbox(v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; size_t v_sz_3861_; size_t v___x_3862_; lean_object* v___x_3863_; lean_object* v_fst_3864_; 
lean_inc_ref(v_args_3856_);
lean_dec_ref_known(v_x_3855_, 3);
v___x_3859_ = lean_box(0);
v___x_3860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3861_ = lean_array_size(v_args_3856_);
v___x_3862_ = ((size_t)0ULL);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3854_, v_args_3856_, v_sz_3861_, v___x_3862_, v___x_3860_);
lean_dec_ref(v_args_3856_);
v_fst_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_fst_3864_);
lean_dec_ref(v___x_3863_);
if (lean_obj_tag(v_fst_3864_) == 0)
{
return v___x_3859_;
}
else
{
lean_object* v_val_3865_; 
v_val_3865_ = lean_ctor_get(v_fst_3864_, 0);
lean_inc(v_val_3865_);
lean_dec_ref_known(v_fst_3864_, 1);
return v_val_3865_;
}
}
else
{
lean_object* v___x_3866_; 
lean_dec_ref(v_p_3854_);
v___x_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3866_, 0, v_x_3855_);
return v___x_3866_;
}
}
else
{
lean_object* v___x_3867_; uint8_t v___x_3868_; 
lean_inc(v_x_3855_);
v___x_3867_ = lean_apply_1(v_p_3854_, v_x_3855_);
v___x_3868_ = lean_unbox(v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec(v_x_3855_);
v___x_3869_ = lean_box(0);
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_x_3855_);
return v___x_3870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3871_, lean_object* v_as_3872_, size_t v_sz_3873_, size_t v_i_3874_, lean_object* v_b_3875_){
_start:
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_usize_dec_lt(v_i_3874_, v_sz_3873_);
if (v___x_3876_ == 0)
{
lean_dec_ref(v_p_3871_);
lean_inc_ref(v_b_3875_);
return v_b_3875_;
}
else
{
lean_object* v___x_3877_; lean_object* v_a_3878_; lean_object* v___x_3879_; 
v___x_3877_ = lean_box(0);
v_a_3878_ = lean_array_uget_borrowed(v_as_3872_, v_i_3874_);
lean_inc(v_a_3878_);
lean_inc_ref(v_p_3871_);
v___x_3879_ = l_Lean_Syntax_findAux(v_p_3871_, v_a_3878_);
if (lean_obj_tag(v___x_3879_) == 1)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_dec_ref(v_p_3871_);
v___x_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
lean_ctor_set(v___x_3881_, 1, v___x_3877_);
return v___x_3881_;
}
else
{
lean_object* v___x_3882_; size_t v___x_3883_; size_t v___x_3884_; 
lean_dec(v___x_3879_);
v___x_3882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3883_ = ((size_t)1ULL);
v___x_3884_ = lean_usize_add(v_i_3874_, v___x_3883_);
v_i_3874_ = v___x_3884_;
v_b_3875_ = v___x_3882_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3886_, lean_object* v_as_3887_, lean_object* v_sz_3888_, lean_object* v_i_3889_, lean_object* v_b_3890_){
_start:
{
size_t v_sz_boxed_3891_; size_t v_i_boxed_3892_; lean_object* v_res_3893_; 
v_sz_boxed_3891_ = lean_unbox_usize(v_sz_3888_);
lean_dec(v_sz_3888_);
v_i_boxed_3892_ = lean_unbox_usize(v_i_3889_);
lean_dec(v_i_3889_);
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3886_, v_as_3887_, v_sz_boxed_3891_, v_i_boxed_3892_, v_b_3890_);
lean_dec_ref(v_b_3890_);
lean_dec_ref(v_as_3887_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3894_, lean_object* v_p_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_Syntax_findAux(v_p_3895_, v_stx_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_Syntax_isNatLit_x3f(v_s_3897_);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_TSyntax_getNat(v_s_3901_);
lean_dec(v_s_3901_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3906_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3908_ = l_Lean_Syntax_isLit_x3f(v___x_3907_, v_stx_3906_);
if (lean_obj_tag(v___x_3908_) == 1)
{
lean_object* v_val_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_val_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3909_, v___x_3910_, v___x_3910_);
lean_dec(v_val_3909_);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; 
lean_dec(v___x_3908_);
v___x_3912_ = lean_box(0);
return v___x_3912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3913_);
lean_dec(v_stx_3913_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3915_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3915_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_TSyntax_getHexNumVal(v_s_3919_);
lean_dec(v_s_3919_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3921_, lean_object* v_p_3922_, lean_object* v_n_3923_){
_start:
{
uint8_t v___x_3924_; 
v___x_3924_ = lean_string_utf8_at_end(v_s_3921_, v_p_3922_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; uint32_t v___x_3926_; uint32_t v___x_3927_; uint8_t v___x_3928_; 
v___x_3925_ = lean_string_utf8_next(v_s_3921_, v_p_3922_);
v___x_3926_ = lean_string_utf8_get(v_s_3921_, v_p_3922_);
lean_dec(v_p_3922_);
v___x_3927_ = 95;
v___x_3928_ = lean_uint32_dec_eq(v___x_3926_, v___x_3927_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_unsigned_to_nat(1u);
v___x_3930_ = lean_nat_add(v_n_3923_, v___x_3929_);
lean_dec(v_n_3923_);
v_p_3922_ = v___x_3925_;
v_n_3923_ = v___x_3930_;
goto _start;
}
else
{
v_p_3922_ = v___x_3925_;
goto _start;
}
}
else
{
lean_dec(v_p_3922_);
return v_n_3923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3933_, lean_object* v_p_3934_, lean_object* v_n_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3933_, v_p_3934_, v_n_3935_);
lean_dec_ref(v_s_3933_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3937_){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3939_ = l_Lean_Syntax_isLit_x3f(v___x_3938_, v_s_3937_);
if (lean_obj_tag(v___x_3939_) == 1)
{
lean_object* v_val_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_val_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_val_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3941_ = lean_unsigned_to_nat(0u);
v___x_3942_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3940_, v___x_3941_, v___x_3941_);
lean_dec(v_val_3940_);
return v___x_3942_;
}
else
{
lean_object* v___x_3943_; 
lean_dec(v___x_3939_);
v___x_3943_ = lean_unsigned_to_nat(0u);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_TSyntax_getHexNumSize(v_s_3944_);
lean_dec(v_s_3944_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_Syntax_getId(v_s_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_TSyntax_getId(v_s_3948_);
lean_dec(v_s_3948_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3957_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v___x_3959_; 
v___x_3959_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_TSyntax_getScientific(v_s_3961_);
lean_dec(v_s_3961_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Syntax_isStrLit_x3f(v_s_3963_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v___x_3965_; 
v___x_3965_ = ((lean_object*)(l_Lean_versionString___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_TSyntax_getString(v_s_3967_);
lean_dec(v_s_3967_);
return v_res_3968_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Syntax_isCharLit_x3f(v_s_3969_);
if (lean_obj_tag(v___x_3970_) == 0)
{
uint32_t v___x_3971_; 
v___x_3971_ = 65;
return v___x_3971_;
}
else
{
lean_object* v_val_3972_; uint32_t v___x_3973_; 
v_val_3972_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_val_3972_);
lean_dec_ref_known(v___x_3970_, 1);
v___x_3973_ = lean_unbox_uint32(v_val_3972_);
lean_dec(v_val_3972_);
return v___x_3973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3974_){
_start:
{
uint32_t v_res_3975_; lean_object* v_r_3976_; 
v_res_3975_ = l_Lean_TSyntax_getChar(v_s_3974_);
lean_dec(v_s_3974_);
v_r_3976_ = lean_box_uint32(v_res_3975_);
return v_r_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lean_Syntax_isNameLit_x3f(v_s_3977_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_box(0);
return v___x_3979_;
}
else
{
lean_object* v_val_3980_; 
v_val_3980_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_val_3980_);
lean_dec_ref_known(v___x_3978_, 1);
return v_val_3980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_TSyntax_getName(v_s_3981_);
lean_dec(v_s_3981_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3983_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_unsigned_to_nat(0u);
v___x_3985_ = l_Lean_Syntax_getArg(v_s_3983_, v___x_3984_);
v___x_3986_ = l_Lean_Syntax_getId(v___x_3985_);
lean_dec(v___x_3985_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_TSyntax_getHygieneInfo(v_s_3987_);
lean_dec(v_s_3987_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3989_, v_a_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3992_, v_a_3993_);
lean_dec_ref(v_a_3993_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3995_){
_start:
{
lean_object* v___f_3996_; 
v___f_3996_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3996_, 0, v_sep_3995_);
return v___f_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3997_, lean_object* v_sep_3998_){
_start:
{
lean_object* v___f_3999_; 
v___f_3999_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3999_, 0, v_sep_3998_);
return v___f_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_4000_, lean_object* v_sep_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_4000_, v_sep_4001_);
lean_dec(v_k_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_4003_, lean_object* v_val_4004_, uint8_t v_canonical_4005_){
_start:
{
lean_object* v___x_4006_; lean_object* v_src_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v_imported_4010_; lean_object* v_ctx_4011_; lean_object* v_scopes_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4028_; 
v___x_4006_ = lean_unsigned_to_nat(0u);
v_src_4007_ = l_Lean_Syntax_getArg(v_s_4003_, v___x_4006_);
v___x_4008_ = l_Lean_Syntax_getId(v_src_4007_);
v___x_4009_ = l_Lean_extractMacroScopes(v___x_4008_);
v_imported_4010_ = lean_ctor_get(v___x_4009_, 1);
v_ctx_4011_ = lean_ctor_get(v___x_4009_, 2);
v_scopes_4012_ = lean_ctor_get(v___x_4009_, 3);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; 
v_unused_4029_ = lean_ctor_get(v___x_4009_, 0);
lean_dec(v_unused_4029_);
v___x_4014_ = v___x_4009_;
v_isShared_4015_ = v_isSharedCheck_4028_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_scopes_4012_);
lean_inc(v_ctx_4011_);
lean_inc(v_imported_4010_);
lean_dec(v___x_4009_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4028_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4016_ = l_Lean_Name_eraseMacroScopes(v_val_4004_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4016_);
v___x_4018_ = v___x_4014_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_imported_4010_);
lean_ctor_set(v_reuseFailAlloc_4027_, 2, v_ctx_4011_);
lean_ctor_set(v_reuseFailAlloc_4027_, 3, v_scopes_4012_);
v___x_4018_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v_id_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_id_4019_ = l_Lean_MacroScopesView_review(v___x_4018_);
v___x_4020_ = l_Lean_SourceInfo_fromRef(v_src_4007_, v_canonical_4005_);
lean_dec(v_src_4007_);
v___x_4021_ = 1;
v___x_4022_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_4004_, v___x_4021_);
v___x_4023_ = lean_string_utf8_byte_size(v___x_4022_);
v___x_4024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4022_);
lean_ctor_set(v___x_4024_, 1, v___x_4006_);
lean_ctor_set(v___x_4024_, 2, v___x_4023_);
v___x_4025_ = lean_box(0);
v___x_4026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4020_);
lean_ctor_set(v___x_4026_, 1, v___x_4024_);
lean_ctor_set(v___x_4026_, 2, v_id_4019_);
lean_ctor_set(v___x_4026_, 3, v___x_4025_);
return v___x_4026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4030_, lean_object* v_val_4031_, lean_object* v_canonical_4032_){
_start:
{
uint8_t v_canonical_boxed_4033_; lean_object* v_res_4034_; 
v_canonical_boxed_4033_ = lean_unbox(v_canonical_4032_);
v_res_4034_ = l_Lean_HygieneInfo_mkIdent(v_s_4030_, v_val_4031_, v_canonical_boxed_4033_);
lean_dec(v_s_4030_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4035_, lean_object* v_inst_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_apply_1(v_inst_4035_, v_a_4037_);
v___x_4039_ = lean_apply_1(v_inst_4036_, v___x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4040_, lean_object* v_inst_4041_){
_start:
{
lean_object* v___f_4042_; 
v___f_4042_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4042_, 0, v_inst_4040_);
lean_closure_set(v___f_4042_, 1, v_inst_4041_);
return v___f_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4043_, lean_object* v_k_4044_, lean_object* v_k_x27_4045_, lean_object* v_inst_4046_, lean_object* v_inst_4047_){
_start:
{
lean_object* v___f_4048_; 
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4048_, 0, v_inst_4046_);
lean_closure_set(v___f_4048_, 1, v_inst_4047_);
return v___f_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4049_, lean_object* v_k_4050_, lean_object* v_k_x27_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4049_, v_k_4050_, v_k_x27_4051_, v_inst_4052_, v_inst_4053_);
lean_dec(v_k_x27_4051_);
lean_dec(v_k_4050_);
return v_res_4054_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4062_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4063_ = l_Lean_mkCIdent(v___x_4062_);
return v___x_4063_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4069_ = l_Lean_mkCIdent(v___x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4070_){
_start:
{
if (v_x_4070_ == 0)
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4071_;
}
else
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4073_){
_start:
{
uint8_t v_x_85__boxed_4074_; lean_object* v_res_4075_; 
v_x_85__boxed_4074_ = lean_unbox(v_x_4073_);
v_res_4075_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4074_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4078_){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_box(2);
v___x_4080_ = l_Lean_Syntax_mkCharLit(v_val_4078_, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4081_){
_start:
{
uint32_t v_val_boxed_4082_; lean_object* v_res_4083_; 
v_val_boxed_4082_ = lean_unbox_uint32(v_val_4081_);
lean_dec(v_val_4081_);
v_res_4083_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4082_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4086_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_box(2);
v___x_4088_ = l_Lean_Syntax_mkStrLit(v_val_4086_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4091_){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = l_Nat_reprFast(v_n_4091_);
v___x_4093_ = lean_box(2);
v___x_4094_ = l_Lean_Syntax_mkNumLit(v___x_4092_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4102_){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4103_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4104_ = lean_substring_tostring(v_s_4102_);
v___x_4105_ = lean_box(2);
v___x_4106_ = l_Lean_Syntax_mkStrLit(v___x_4104_, v___x_4105_);
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = lean_mk_empty_array_with_capacity(v___x_4107_);
v___x_4109_ = lean_array_push(v___x_4108_, v___x_4106_);
v___x_4110_ = l_Lean_Syntax_mkCApp(v___x_4103_, v___x_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4113_, lean_object* v_x_4114_){
_start:
{
switch(lean_obj_tag(v_x_4114_))
{
case 0:
{
uint8_t v___x_4115_; 
v___x_4115_ = l_List_isEmpty___redArg(v_acc_4113_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_acc_4113_);
return v___x_4116_;
}
else
{
lean_object* v___x_4117_; 
lean_dec(v_acc_4113_);
v___x_4117_ = lean_box(0);
return v___x_4117_;
}
}
case 1:
{
lean_object* v_pre_4118_; lean_object* v_str_4119_; lean_object* v_val_4121_; lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
v_pre_4118_ = lean_ctor_get(v_x_4114_, 0);
lean_inc(v_pre_4118_);
v_str_4119_ = lean_ctor_get(v_x_4114_, 1);
lean_inc_ref(v_str_4119_);
lean_dec_ref_known(v_x_4114_, 2);
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = lean_string_utf8_byte_size(v_str_4119_);
v___x_4126_ = lean_nat_dec_lt(v___x_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4127_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4128_ = lean_string_append(v___x_4127_, v_str_4119_);
lean_dec_ref(v_str_4119_);
v___x_4129_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
v_val_4121_ = v___x_4130_;
goto v___jp_4120_;
}
else
{
lean_object* v___f_4131_; lean_object* v___f_4132_; uint8_t v___y_4146_; uint32_t v___y_4148_; uint8_t v___y_4149_; uint32_t v___y_4154_; uint8_t v___y_4160_; uint8_t v_c_4169_; uint8_t v___y_4171_; uint8_t v___y_4175_; uint8_t v___x_4180_; uint8_t v___x_4181_; 
v___f_4131_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v___f_4132_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v_c_4169_ = lean_string_get_byte_fast(v_str_4119_, v___x_4124_);
v___x_4180_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4181_ = lean_uint8_dec_le(v___x_4180_, v_c_4169_);
if (v___x_4181_ == 0)
{
v___y_4175_ = v___x_4181_;
goto v___jp_4174_;
}
else
{
uint8_t v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4183_ = lean_uint8_dec_le(v_c_4169_, v___x_4182_);
v___y_4175_ = v___x_4183_;
goto v___jp_4174_;
}
v___jp_4133_:
{
uint8_t v___x_4134_; 
lean_inc_ref(v_str_4119_);
v___x_4134_ = lean_string_any(v_str_4119_, v___f_4132_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4135_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4136_ = lean_string_append(v___x_4135_, v_str_4119_);
lean_dec_ref(v_str_4119_);
v___x_4137_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4138_ = lean_string_append(v___x_4136_, v___x_4137_);
v_val_4121_ = v___x_4138_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4139_; 
lean_dec_ref(v_str_4119_);
lean_dec(v_pre_4118_);
lean_dec(v_acc_4113_);
v___x_4139_ = lean_box(0);
return v___x_4139_;
}
}
v___jp_4140_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; 
lean_inc_ref(v_str_4119_);
v___x_4141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4141_, 0, v_str_4119_);
lean_ctor_set(v___x_4141_, 1, v___x_4124_);
lean_ctor_set(v___x_4141_, 2, v___x_4125_);
v___x_4142_ = lean_unsigned_to_nat(1u);
v___x_4143_ = lean_substring_drop(v___x_4141_, v___x_4142_);
v___x_4144_ = lean_substring_all(v___x_4143_, v___f_4131_);
if (v___x_4144_ == 0)
{
goto v___jp_4133_;
}
else
{
v_val_4121_ = v_str_4119_;
goto v___jp_4120_;
}
}
v___jp_4145_:
{
if (v___y_4146_ == 0)
{
goto v___jp_4133_;
}
else
{
goto v___jp_4140_;
}
}
v___jp_4147_:
{
if (v___y_4149_ == 0)
{
uint32_t v___x_4150_; uint8_t v___x_4151_; 
v___x_4150_ = 95;
v___x_4151_ = lean_uint32_dec_eq(v___y_4148_, v___x_4150_);
if (v___x_4151_ == 0)
{
uint8_t v___x_4152_; 
v___x_4152_ = l_Lean_isLetterLike(v___y_4148_);
v___y_4146_ = v___x_4152_;
goto v___jp_4145_;
}
else
{
v___y_4146_ = v___x_4151_;
goto v___jp_4145_;
}
}
else
{
goto v___jp_4140_;
}
}
v___jp_4153_:
{
uint32_t v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = 97;
v___x_4156_ = lean_uint32_dec_le(v___x_4155_, v___y_4154_);
if (v___x_4156_ == 0)
{
v___y_4148_ = v___y_4154_;
v___y_4149_ = v___x_4156_;
goto v___jp_4147_;
}
else
{
uint32_t v___x_4157_; uint8_t v___x_4158_; 
v___x_4157_ = 122;
v___x_4158_ = lean_uint32_dec_le(v___y_4154_, v___x_4157_);
v___y_4148_ = v___y_4154_;
v___y_4149_ = v___x_4158_;
goto v___jp_4147_;
}
}
v___jp_4159_:
{
if (v___y_4160_ == 0)
{
uint32_t v___x_4161_; uint32_t v___x_4162_; uint8_t v___x_4163_; 
v___x_4161_ = lean_string_utf8_get(v_str_4119_, v___x_4124_);
v___x_4162_ = 65;
v___x_4163_ = lean_uint32_dec_le(v___x_4162_, v___x_4161_);
if (v___x_4163_ == 0)
{
v___y_4154_ = v___x_4161_;
goto v___jp_4153_;
}
else
{
uint32_t v___x_4164_; uint8_t v___x_4165_; 
v___x_4164_ = 90;
v___x_4165_ = lean_uint32_dec_le(v___x_4161_, v___x_4164_);
if (v___x_4165_ == 0)
{
v___y_4154_ = v___x_4161_;
goto v___jp_4153_;
}
else
{
goto v___jp_4140_;
}
}
}
else
{
v_val_4121_ = v_str_4119_;
goto v___jp_4120_;
}
}
v___jp_4166_:
{
lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4119_, v___x_4167_);
v___y_4160_ = v___x_4168_;
goto v___jp_4159_;
}
v___jp_4170_:
{
if (v___y_4171_ == 0)
{
uint8_t v___x_4172_; uint8_t v___x_4173_; 
v___x_4172_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4173_ = lean_uint8_dec_eq(v_c_4169_, v___x_4172_);
if (v___x_4173_ == 0)
{
v___y_4160_ = v___x_4173_;
goto v___jp_4159_;
}
else
{
goto v___jp_4166_;
}
}
else
{
goto v___jp_4166_;
}
}
v___jp_4174_:
{
if (v___y_4175_ == 0)
{
uint8_t v___x_4176_; uint8_t v___x_4177_; 
v___x_4176_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4177_ = lean_uint8_dec_le(v___x_4176_, v_c_4169_);
if (v___x_4177_ == 0)
{
v___y_4171_ = v___x_4177_;
goto v___jp_4170_;
}
else
{
uint8_t v___x_4178_; uint8_t v___x_4179_; 
v___x_4178_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4179_ = lean_uint8_dec_le(v_c_4169_, v___x_4178_);
v___y_4171_ = v___x_4179_;
goto v___jp_4170_;
}
}
else
{
goto v___jp_4166_;
}
}
}
v___jp_4120_:
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4122_, 0, v_val_4121_);
lean_ctor_set(v___x_4122_, 1, v_acc_4113_);
v_acc_4113_ = v___x_4122_;
v_x_4114_ = v_pre_4118_;
goto _start;
}
}
default: 
{
lean_object* v___x_4184_; 
lean_dec_ref_known(v_x_4114_, 2);
lean_dec(v_acc_4113_);
v___x_4184_ = lean_box(0);
return v___x_4184_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4192_ = l_Lean_mkCIdent(v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4203_){
_start:
{
switch(lean_obj_tag(v_x_4203_))
{
case 0:
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4204_;
}
case 1:
{
lean_object* v_pre_4205_; lean_object* v_str_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_pre_4205_ = lean_ctor_get(v_x_4203_, 0);
lean_inc(v_pre_4205_);
v_str_4206_ = lean_ctor_get(v_x_4203_, 1);
lean_inc_ref(v_str_4206_);
lean_dec_ref_known(v_x_4203_, 2);
v___x_4207_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4208_ = l_Lean_quoteNameMk(v_pre_4205_);
v___x_4209_ = lean_box(2);
v___x_4210_ = l_Lean_Syntax_mkStrLit(v_str_4206_, v___x_4209_);
v___x_4211_ = lean_unsigned_to_nat(2u);
v___x_4212_ = lean_mk_empty_array_with_capacity(v___x_4211_);
v___x_4213_ = lean_array_push(v___x_4212_, v___x_4208_);
v___x_4214_ = lean_array_push(v___x_4213_, v___x_4210_);
v___x_4215_ = l_Lean_Syntax_mkCApp(v___x_4207_, v___x_4214_);
return v___x_4215_;
}
default: 
{
lean_object* v_pre_4216_; lean_object* v_i_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_pre_4216_ = lean_ctor_get(v_x_4203_, 0);
lean_inc(v_pre_4216_);
v_i_4217_ = lean_ctor_get(v_x_4203_, 1);
lean_inc(v_i_4217_);
lean_dec_ref_known(v_x_4203_, 2);
v___x_4218_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4219_ = l_Lean_quoteNameMk(v_pre_4216_);
v___x_4220_ = l_Nat_reprFast(v_i_4217_);
v___x_4221_ = lean_box(2);
v___x_4222_ = l_Lean_Syntax_mkNumLit(v___x_4220_, v___x_4221_);
v___x_4223_ = lean_unsigned_to_nat(2u);
v___x_4224_ = lean_mk_empty_array_with_capacity(v___x_4223_);
v___x_4225_ = lean_array_push(v___x_4224_, v___x_4219_);
v___x_4226_ = lean_array_push(v___x_4225_, v___x_4222_);
v___x_4227_ = l_Lean_Syntax_mkCApp(v___x_4218_, v___x_4226_);
return v___x_4227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4234_){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_box(0);
lean_inc(v_n_4234_);
v___x_4236_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4235_, v_n_4234_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_quoteNameMk(v_n_4234_);
return v___x_4237_;
}
else
{
lean_object* v_val_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_dec(v_n_4234_);
v_val_4238_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_val_4238_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4239_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4240_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4241_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4242_ = lean_string_intercalate(v___x_4241_, v_val_4238_);
v___x_4243_ = lean_string_append(v___x_4240_, v___x_4242_);
lean_dec_ref(v___x_4242_);
v___x_4244_ = lean_box(2);
v___x_4245_ = l_Lean_Syntax_mkNameLit(v___x_4243_, v___x_4244_);
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_mk_empty_array_with_capacity(v___x_4246_);
v___x_4248_ = lean_array_push(v___x_4247_, v___x_4245_);
v___x_4249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4244_);
lean_ctor_set(v___x_4249_, 1, v___x_4239_);
lean_ctor_set(v___x_4249_, 2, v___x_4248_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4250_){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = lean_box(0);
lean_inc(v_n_4250_);
v___x_4252_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4251_, v_n_4250_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_quoteNameMk(v_n_4250_);
return v___x_4253_;
}
else
{
lean_object* v_val_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_dec(v_n_4250_);
v_val_4254_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_val_4254_);
lean_dec_ref_known(v___x_4252_, 1);
v___x_4255_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4256_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4257_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4258_ = lean_string_intercalate(v___x_4257_, v_val_4254_);
v___x_4259_ = lean_string_append(v___x_4256_, v___x_4258_);
lean_dec_ref(v___x_4258_);
v___x_4260_ = lean_box(2);
v___x_4261_ = l_Lean_Syntax_mkNameLit(v___x_4259_, v___x_4260_);
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_mk_empty_array_with_capacity(v___x_4262_);
v___x_4264_ = lean_array_push(v___x_4263_, v___x_4261_);
v___x_4265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4260_);
lean_ctor_set(v___x_4265_, 1, v___x_4255_);
lean_ctor_set(v___x_4265_, 2, v___x_4264_);
return v___x_4265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4273_, lean_object* v_inst_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v_fst_4276_; lean_object* v_snd_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v_fst_4276_ = lean_ctor_get(v_x_4275_, 0);
lean_inc(v_fst_4276_);
v_snd_4277_ = lean_ctor_get(v_x_4275_, 1);
lean_inc(v_snd_4277_);
lean_dec_ref(v_x_4275_);
v___x_4278_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4279_ = lean_apply_1(v_inst_4273_, v_fst_4276_);
v___x_4280_ = lean_apply_1(v_inst_4274_, v_snd_4277_);
v___x_4281_ = lean_unsigned_to_nat(2u);
v___x_4282_ = lean_mk_empty_array_with_capacity(v___x_4281_);
v___x_4283_ = lean_array_push(v___x_4282_, v___x_4279_);
v___x_4284_ = lean_array_push(v___x_4283_, v___x_4280_);
v___x_4285_ = l_Lean_Syntax_mkCApp(v___x_4278_, v___x_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4286_, lean_object* v_inst_4287_){
_start:
{
lean_object* v___f_4288_; 
v___f_4288_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4288_, 0, v_inst_4286_);
lean_closure_set(v___f_4288_, 1, v_inst_4287_);
return v___f_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4289_, lean_object* v_00_u03b2_4290_, lean_object* v_inst_4291_, lean_object* v_inst_4292_){
_start:
{
lean_object* v___f_4293_; 
v___f_4293_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4293_, 0, v_inst_4291_);
lean_closure_set(v___f_4293_, 1, v_inst_4292_);
return v___f_4293_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4300_ = l_Lean_mkCIdent(v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4305_, lean_object* v_x_4306_){
_start:
{
if (lean_obj_tag(v_x_4306_) == 0)
{
lean_object* v___x_4307_; 
lean_dec_ref(v_inst_4305_);
v___x_4307_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4307_;
}
else
{
lean_object* v_head_4308_; lean_object* v_tail_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_head_4308_ = lean_ctor_get(v_x_4306_, 0);
lean_inc(v_head_4308_);
v_tail_4309_ = lean_ctor_get(v_x_4306_, 1);
lean_inc(v_tail_4309_);
lean_dec_ref_known(v_x_4306_, 2);
v___x_4310_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4305_);
v___x_4311_ = lean_apply_1(v_inst_4305_, v_head_4308_);
v___x_4312_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4305_, v_tail_4309_);
v___x_4313_ = lean_unsigned_to_nat(2u);
v___x_4314_ = lean_mk_empty_array_with_capacity(v___x_4313_);
v___x_4315_ = lean_array_push(v___x_4314_, v___x_4311_);
v___x_4316_ = lean_array_push(v___x_4315_, v___x_4312_);
v___x_4317_ = l_Lean_Syntax_mkCApp(v___x_4310_, v___x_4316_);
return v___x_4317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4318_, lean_object* v_inst_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4319_, v_x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4322_, v_a_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4325_, lean_object* v_inst_4326_, lean_object* v_a_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4326_, v_a_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4330_, 0, lean_box(0));
lean_closure_set(v___x_4330_, 1, v_inst_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4331_, lean_object* v_inst_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4333_, 0, lean_box(0));
lean_closure_set(v___x_4333_, 1, v_inst_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4336_, lean_object* v_xs_4337_, lean_object* v_i_4338_, lean_object* v_args_4339_){
_start:
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = lean_array_get_size(v_xs_4337_);
v___x_4341_ = lean_nat_dec_lt(v_i_4338_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
lean_dec(v_i_4338_);
lean_dec_ref(v_inst_4336_);
v___x_4342_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4343_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4344_ = l_Nat_reprFast(v___x_4340_);
v___x_4345_ = lean_string_append(v___x_4343_, v___x_4344_);
lean_dec_ref(v___x_4344_);
v___x_4346_ = l_Lean_Name_mkStr2(v___x_4342_, v___x_4345_);
v___x_4347_ = l_Lean_Syntax_mkCApp(v___x_4346_, v_args_4339_);
return v___x_4347_;
}
else
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4348_ = lean_unsigned_to_nat(1u);
v___x_4349_ = lean_nat_add(v_i_4338_, v___x_4348_);
v___x_4350_ = lean_array_fget_borrowed(v_xs_4337_, v_i_4338_);
lean_dec(v_i_4338_);
lean_inc_ref(v_inst_4336_);
lean_inc(v___x_4350_);
v___x_4351_ = lean_apply_1(v_inst_4336_, v___x_4350_);
v___x_4352_ = lean_array_push(v_args_4339_, v___x_4351_);
v_i_4338_ = v___x_4349_;
v_args_4339_ = v___x_4352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4354_, lean_object* v_xs_4355_, lean_object* v_i_4356_, lean_object* v_args_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4354_, v_xs_4355_, v_i_4356_, v_args_4357_);
lean_dec_ref(v_xs_4355_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4359_, lean_object* v_inst_4360_, lean_object* v_xs_4361_, lean_object* v_i_4362_, lean_object* v_args_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4360_, v_xs_4361_, v_i_4362_, v_args_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4365_, lean_object* v_inst_4366_, lean_object* v_xs_4367_, lean_object* v_i_4368_, lean_object* v_args_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4365_, v_inst_4366_, v_xs_4367_, v_i_4368_, v_args_4369_);
lean_dec_ref(v_xs_4367_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4375_, lean_object* v_xs_4376_){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4377_ = lean_array_get_size(v_xs_4376_);
v___x_4378_ = lean_unsigned_to_nat(8u);
v___x_4379_ = lean_nat_dec_le(v___x_4377_, v___x_4378_);
if (v___x_4379_ == 0)
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4380_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4381_ = lean_array_to_list(v_xs_4376_);
v___x_4382_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4375_, v___x_4381_);
v___x_4383_ = lean_unsigned_to_nat(1u);
v___x_4384_ = lean_mk_empty_array_with_capacity(v___x_4383_);
v___x_4385_ = lean_array_push(v___x_4384_, v___x_4382_);
v___x_4386_ = l_Lean_Syntax_mkCApp(v___x_4380_, v___x_4385_);
return v___x_4386_;
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4387_ = lean_unsigned_to_nat(0u);
v___x_4388_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4389_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4375_, v_xs_4376_, v___x_4387_, v___x_4388_);
lean_dec_ref(v_xs_4376_);
return v___x_4389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4390_, lean_object* v_inst_4391_, lean_object* v_xs_4392_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4391_, v_xs_4392_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4394_, lean_object* v_xs_4395_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4394_, v_xs_4395_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4397_, lean_object* v_inst_4398_, lean_object* v_xs_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4398_, v_xs_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4402_, 0, lean_box(0));
lean_closure_set(v___x_4402_, 1, v_inst_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4403_, lean_object* v_inst_4404_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4405_, 0, lean_box(0));
lean_closure_set(v___x_4405_, 1, v_inst_4404_);
return v___x_4405_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4412_ = l_Lean_mkIdent(v___x_4411_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4417_, lean_object* v_x_4418_){
_start:
{
if (lean_obj_tag(v_x_4418_) == 0)
{
lean_object* v___x_4419_; 
lean_dec_ref(v_inst_4417_);
v___x_4419_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4419_;
}
else
{
lean_object* v_val_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v_val_4420_ = lean_ctor_get(v_x_4418_, 0);
lean_inc(v_val_4420_);
lean_dec_ref_known(v_x_4418_, 1);
v___x_4421_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4422_ = lean_apply_1(v_inst_4417_, v_val_4420_);
v___x_4423_ = lean_unsigned_to_nat(1u);
v___x_4424_ = lean_mk_empty_array_with_capacity(v___x_4423_);
v___x_4425_ = lean_array_push(v___x_4424_, v___x_4422_);
v___x_4426_ = l_Lean_Syntax_mkCApp(v___x_4421_, v___x_4425_);
return v___x_4426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4427_){
_start:
{
lean_object* v___f_4428_; 
v___f_4428_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4428_, 0, v_inst_4427_);
return v___f_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4429_, lean_object* v_inst_4430_){
_start:
{
lean_object* v___f_4431_; 
v___f_4431_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4431_, 0, v_inst_4430_);
return v___f_4431_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4432_, lean_object* v_k_4433_){
_start:
{
lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4434_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4435_ = lean_name_eq(v_k_4433_, v___x_4434_);
if (v___x_4435_ == 0)
{
uint8_t v___x_4436_; 
v___x_4436_ = 1;
return v___x_4436_;
}
else
{
return v___x_4432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4437_, lean_object* v_k_4438_){
_start:
{
uint8_t v___x_436__boxed_4439_; uint8_t v_res_4440_; lean_object* v_r_4441_; 
v___x_436__boxed_4439_ = lean_unbox(v___x_4437_);
v_res_4440_ = l_Lean_evalPrec___lam__0(v___x_436__boxed_4439_, v_k_4438_);
lean_dec(v_k_4438_);
v_r_4441_ = lean_box(v_res_4440_);
return v_r_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v_methods_4446_; lean_object* v_quotContext_4447_; lean_object* v_currMacroScope_4448_; lean_object* v_currRecDepth_4449_; lean_object* v_maxRecDepth_4450_; lean_object* v_ref_4451_; uint8_t v___x_4452_; 
v_methods_4446_ = lean_ctor_get(v_a_4444_, 0);
v_quotContext_4447_ = lean_ctor_get(v_a_4444_, 1);
v_currMacroScope_4448_ = lean_ctor_get(v_a_4444_, 2);
v_currRecDepth_4449_ = lean_ctor_get(v_a_4444_, 3);
v_maxRecDepth_4450_ = lean_ctor_get(v_a_4444_, 4);
v_ref_4451_ = lean_ctor_get(v_a_4444_, 5);
v___x_4452_ = lean_nat_dec_eq(v_currRecDepth_4449_, v_maxRecDepth_4450_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; lean_object* v___f_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4453_ = lean_box(v___x_4452_);
v___f_4454_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4454_, 0, v___x_4453_);
v___x_4455_ = lean_unsigned_to_nat(1u);
v___x_4456_ = lean_nat_add(v_currRecDepth_4449_, v___x_4455_);
lean_inc(v_ref_4451_);
lean_inc(v_maxRecDepth_4450_);
lean_inc(v_currMacroScope_4448_);
lean_inc(v_quotContext_4447_);
lean_inc(v_methods_4446_);
v___x_4457_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4457_, 0, v_methods_4446_);
lean_ctor_set(v___x_4457_, 1, v_quotContext_4447_);
lean_ctor_set(v___x_4457_, 2, v_currMacroScope_4448_);
lean_ctor_set(v___x_4457_, 3, v___x_4456_);
lean_ctor_set(v___x_4457_, 4, v_maxRecDepth_4450_);
lean_ctor_set(v___x_4457_, 5, v_ref_4451_);
lean_inc_ref(v___x_4457_);
v___x_4458_ = l_Lean_expandMacros(v_stx_4443_, v___f_4454_, v___x_4457_, v_a_4445_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4472_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_a_4460_ = lean_ctor_get(v___x_4458_, 1);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4462_ = v___x_4458_;
v_isShared_4463_ = v_isSharedCheck_4472_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4472_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4464_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4459_);
v___x_4465_ = l_Lean_Syntax_isOfKind(v_a_4459_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
lean_del_object(v___x_4462_);
v___x_4466_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4467_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4459_, v___x_4466_, v___x_4457_, v_a_4460_);
lean_dec_ref_known(v___x_4457_, 6);
lean_dec(v_a_4459_);
return v___x_4467_;
}
else
{
lean_object* v___x_4468_; lean_object* v___x_4470_; 
lean_dec_ref_known(v___x_4457_, 6);
v___x_4468_ = l_Lean_TSyntax_getNat(v_a_4459_);
lean_dec(v_a_4459_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4468_);
v___x_4470_ = v___x_4462_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_a_4460_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec_ref_known(v___x_4457_, 6);
v_a_4473_ = lean_ctor_get(v___x_4458_, 0);
v_a_4474_ = lean_ctor_get(v___x_4458_, 1);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4458_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_inc(v_a_4473_);
lean_dec(v___x_4458_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4473_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_a_4474_);
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
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4482_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4483_, 0, v_stx_4443_);
lean_ctor_set(v___x_4483_, 1, v___x_4482_);
v___x_4484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
lean_ctor_set(v___x_4484_, 1, v_a_4445_);
return v___x_4484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_evalPrec(v_stx_4485_, v_a_4486_, v_a_4487_);
lean_dec_ref(v_a_4486_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_methods_4493_; lean_object* v_quotContext_4494_; lean_object* v_currMacroScope_4495_; lean_object* v_currRecDepth_4496_; lean_object* v_maxRecDepth_4497_; lean_object* v_ref_4498_; uint8_t v___x_4499_; 
v_methods_4493_ = lean_ctor_get(v_a_4491_, 0);
v_quotContext_4494_ = lean_ctor_get(v_a_4491_, 1);
v_currMacroScope_4495_ = lean_ctor_get(v_a_4491_, 2);
v_currRecDepth_4496_ = lean_ctor_get(v_a_4491_, 3);
v_maxRecDepth_4497_ = lean_ctor_get(v_a_4491_, 4);
v_ref_4498_ = lean_ctor_get(v_a_4491_, 5);
v___x_4499_ = lean_nat_dec_eq(v_currRecDepth_4496_, v_maxRecDepth_4497_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; lean_object* v___f_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4500_ = lean_box(v___x_4499_);
v___f_4501_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4501_, 0, v___x_4500_);
v___x_4502_ = lean_unsigned_to_nat(1u);
v___x_4503_ = lean_nat_add(v_currRecDepth_4496_, v___x_4502_);
lean_inc(v_ref_4498_);
lean_inc(v_maxRecDepth_4497_);
lean_inc(v_currMacroScope_4495_);
lean_inc(v_quotContext_4494_);
lean_inc(v_methods_4493_);
v___x_4504_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4504_, 0, v_methods_4493_);
lean_ctor_set(v___x_4504_, 1, v_quotContext_4494_);
lean_ctor_set(v___x_4504_, 2, v_currMacroScope_4495_);
lean_ctor_set(v___x_4504_, 3, v___x_4503_);
lean_ctor_set(v___x_4504_, 4, v_maxRecDepth_4497_);
lean_ctor_set(v___x_4504_, 5, v_ref_4498_);
lean_inc_ref(v___x_4504_);
v___x_4505_ = l_Lean_expandMacros(v_stx_4490_, v___f_4501_, v___x_4504_, v_a_4492_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4519_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
v_a_4507_ = lean_ctor_get(v___x_4505_, 1);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4509_ = v___x_4505_;
v_isShared_4510_ = v_isSharedCheck_4519_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_inc(v_a_4506_);
lean_dec(v___x_4505_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4519_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4506_);
v___x_4512_ = l_Lean_Syntax_isOfKind(v_a_4506_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_del_object(v___x_4509_);
v___x_4513_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4514_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4506_, v___x_4513_, v___x_4504_, v_a_4507_);
lean_dec_ref_known(v___x_4504_, 6);
lean_dec(v_a_4506_);
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4517_; 
lean_dec_ref_known(v___x_4504_, 6);
v___x_4515_ = l_Lean_TSyntax_getNat(v_a_4506_);
lean_dec(v_a_4506_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 0, v___x_4515_);
v___x_4517_ = v___x_4509_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4515_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_a_4507_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec_ref_known(v___x_4504_, 6);
v_a_4520_ = lean_ctor_get(v___x_4505_, 0);
v_a_4521_ = lean_ctor_get(v___x_4505_, 1);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4505_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_inc(v_a_4520_);
lean_dec(v___x_4505_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4520_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_a_4521_);
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
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4530_, 0, v_stx_4490_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
v___x_4531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
lean_ctor_set(v___x_4531_, 1, v_a_4492_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_evalPrio(v_stx_4532_, v_a_4533_, v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
if (lean_obj_tag(v_x_4536_) == 0)
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = lean_unsigned_to_nat(1000u);
v___x_4540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
lean_ctor_set(v___x_4540_, 1, v_a_4538_);
return v___x_4540_;
}
else
{
lean_object* v_val_4541_; lean_object* v___x_4542_; 
v_val_4541_ = lean_ctor_get(v_x_4536_, 0);
lean_inc(v_val_4541_);
lean_dec_ref_known(v_x_4536_, 1);
v___x_4542_ = l_Lean_evalPrio(v_val_4541_, v_a_4537_, v_a_4538_);
return v___x_4542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_evalOptPrio(v_x_4543_, v_a_4544_, v_a_4545_);
lean_dec_ref(v_a_4544_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4547_, lean_object* v_x1_4548_, lean_object* v_x2_4549_){
_start:
{
lean_object* v_fst_4550_; uint8_t v___x_4551_; 
v_fst_4550_ = lean_ctor_get(v_x1_4548_, 0);
v___x_4551_ = lean_unbox(v_fst_4550_);
if (v___x_4551_ == 0)
{
lean_object* v_snd_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v_x2_4549_);
v_snd_4552_ = lean_ctor_get(v_x1_4548_, 1);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_x1_4548_);
if (v_isSharedCheck_4560_ == 0)
{
lean_object* v_unused_4561_; 
v_unused_4561_ = lean_ctor_get(v_x1_4548_, 0);
lean_dec(v_unused_4561_);
v___x_4554_ = v_x1_4548_;
v_isShared_4555_ = v_isSharedCheck_4560_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_snd_4552_);
lean_dec(v_x1_4548_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4560_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4556_ = lean_box(v___x_4547_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4556_);
v___x_4558_ = v___x_4554_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v_snd_4552_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
else
{
lean_object* v_snd_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4572_; 
v_snd_4562_ = lean_ctor_get(v_x1_4548_, 1);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_x1_4548_);
if (v_isSharedCheck_4572_ == 0)
{
lean_object* v_unused_4573_; 
v_unused_4573_ = lean_ctor_get(v_x1_4548_, 0);
lean_dec(v_unused_4573_);
v___x_4564_ = v_x1_4548_;
v_isShared_4565_ = v_isSharedCheck_4572_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_snd_4562_);
lean_dec(v_x1_4548_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4572_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
uint8_t v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4570_; 
v___x_4566_ = 0;
v___x_4567_ = lean_array_push(v_snd_4562_, v_x2_4549_);
v___x_4568_ = lean_box(v___x_4566_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 1, v___x_4567_);
lean_ctor_set(v___x_4564_, 0, v___x_4568_);
v___x_4570_ = v___x_4564_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
lean_ctor_set(v_reuseFailAlloc_4571_, 1, v___x_4567_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4574_, lean_object* v_x1_4575_, lean_object* v_x2_4576_){
_start:
{
uint8_t v___x_96__boxed_4577_; lean_object* v_res_4578_; 
v___x_96__boxed_4577_ = lean_unbox(v___x_4574_);
v_res_4578_ = l_Array_getSepElems___redArg___lam__0(v___x_96__boxed_4577_, v_x1_4575_, v_x2_4576_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4600_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4601_ = lean_unsigned_to_nat(0u);
v___x_4602_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4603_ = lean_array_get_size(v_as_4600_);
v___x_4604_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4605_ = lean_nat_dec_lt(v___x_4601_, v___x_4603_);
if (v___x_4605_ == 0)
{
lean_dec_ref(v_as_4600_);
return v___x_4602_;
}
else
{
lean_object* v___x_4606_; lean_object* v___f_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; uint8_t v___x_4610_; 
v___x_4606_ = lean_box(v___x_4605_);
v___f_4607_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4607_, 0, v___x_4606_);
v___x_4608_ = lean_box(v___x_4605_);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set(v___x_4609_, 1, v___x_4602_);
v___x_4610_ = lean_nat_dec_le(v___x_4603_, v___x_4603_);
if (v___x_4610_ == 0)
{
if (v___x_4605_ == 0)
{
lean_dec_ref_known(v___x_4609_, 2);
lean_dec_ref(v___f_4607_);
lean_dec_ref(v_as_4600_);
return v___x_4602_;
}
else
{
size_t v___x_4611_; size_t v___x_4612_; lean_object* v___x_4613_; lean_object* v_snd_4614_; 
v___x_4611_ = ((size_t)0ULL);
v___x_4612_ = lean_usize_of_nat(v___x_4603_);
v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4604_, v___f_4607_, v_as_4600_, v___x_4611_, v___x_4612_, v___x_4609_);
v_snd_4614_ = lean_ctor_get(v___x_4613_, 1);
lean_inc(v_snd_4614_);
lean_dec(v___x_4613_);
return v_snd_4614_;
}
}
else
{
size_t v___x_4615_; size_t v___x_4616_; lean_object* v___x_4617_; lean_object* v_snd_4618_; 
v___x_4615_ = ((size_t)0ULL);
v___x_4616_ = lean_usize_of_nat(v___x_4603_);
v___x_4617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4604_, v___f_4607_, v_as_4600_, v___x_4615_, v___x_4616_, v___x_4609_);
v_snd_4618_ = lean_ctor_get(v___x_4617_, 1);
lean_inc(v_snd_4618_);
lean_dec(v___x_4617_);
return v_snd_4618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4619_, lean_object* v_as_4620_){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4623_ = lean_array_get_size(v_as_4620_);
v___x_4624_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4625_ = lean_nat_dec_lt(v___x_4621_, v___x_4623_);
if (v___x_4625_ == 0)
{
lean_dec_ref(v_as_4620_);
return v___x_4622_;
}
else
{
lean_object* v___x_4626_; lean_object* v___f_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; 
v___x_4626_ = lean_box(v___x_4625_);
v___f_4627_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4627_, 0, v___x_4626_);
v___x_4628_ = lean_box(v___x_4625_);
v___x_4629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
lean_ctor_set(v___x_4629_, 1, v___x_4622_);
v___x_4630_ = lean_nat_dec_le(v___x_4623_, v___x_4623_);
if (v___x_4630_ == 0)
{
if (v___x_4625_ == 0)
{
lean_dec_ref_known(v___x_4629_, 2);
lean_dec_ref(v___f_4627_);
lean_dec_ref(v_as_4620_);
return v___x_4622_;
}
else
{
size_t v___x_4631_; size_t v___x_4632_; lean_object* v___x_4633_; lean_object* v_snd_4634_; 
v___x_4631_ = ((size_t)0ULL);
v___x_4632_ = lean_usize_of_nat(v___x_4623_);
v___x_4633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4624_, v___f_4627_, v_as_4620_, v___x_4631_, v___x_4632_, v___x_4629_);
v_snd_4634_ = lean_ctor_get(v___x_4633_, 1);
lean_inc(v_snd_4634_);
lean_dec(v___x_4633_);
return v_snd_4634_;
}
}
else
{
size_t v___x_4635_; size_t v___x_4636_; lean_object* v___x_4637_; lean_object* v_snd_4638_; 
v___x_4635_ = ((size_t)0ULL);
v___x_4636_ = lean_usize_of_nat(v___x_4623_);
v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4624_, v___f_4627_, v_as_4620_, v___x_4635_, v___x_4636_, v___x_4629_);
v_snd_4638_ = lean_ctor_get(v___x_4637_, 1);
lean_inc(v_snd_4638_);
lean_dec(v___x_4637_);
return v_snd_4638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4639_, lean_object* v_inst_4640_, lean_object* v_a_4641_, lean_object* v_p_4642_, lean_object* v_acc_4643_, lean_object* v_stx_4644_, uint8_t v_____do__lift_4645_){
_start:
{
if (v_____do__lift_4645_ == 0)
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
lean_dec(v_stx_4644_);
v___x_4654_ = lean_unsigned_to_nat(2u);
v___x_4655_ = lean_nat_add(v_i_4639_, v___x_4654_);
v___x_4656_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4640_, v_a_4641_, v_p_4642_, v___x_4655_, v_acc_4643_);
return v___x_4656_;
}
else
{
lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4657_ = lean_array_get_size(v_acc_4643_);
v___x_4658_ = lean_unsigned_to_nat(0u);
v___x_4659_ = lean_nat_dec_eq(v___x_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
uint8_t v___x_4660_; 
v___x_4660_ = lean_nat_dec_eq(v_i_4639_, v___x_4658_);
if (v___x_4660_ == 0)
{
goto v___jp_4646_;
}
else
{
if (v___x_4659_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = lean_unsigned_to_nat(2u);
v___x_4662_ = lean_nat_add(v_i_4639_, v___x_4661_);
v___x_4663_ = lean_array_push(v_acc_4643_, v_stx_4644_);
v___x_4664_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4640_, v_a_4641_, v_p_4642_, v___x_4662_, v___x_4663_);
return v___x_4664_;
}
else
{
goto v___jp_4646_;
}
}
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4665_ = lean_unsigned_to_nat(2u);
v___x_4666_ = lean_nat_add(v_i_4639_, v___x_4665_);
v___x_4667_ = lean_array_push(v_acc_4643_, v_stx_4644_);
v___x_4668_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4640_, v_a_4641_, v_p_4642_, v___x_4666_, v___x_4667_);
return v___x_4668_;
}
}
v___jp_4646_:
{
lean_object* v___x_4647_; lean_object* v_sepStx_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4647_ = lean_nat_pred(v_i_4639_);
v_sepStx_4648_ = lean_array_fget_borrowed(v_a_4641_, v___x_4647_);
lean_dec(v___x_4647_);
v___x_4649_ = lean_unsigned_to_nat(2u);
v___x_4650_ = lean_nat_add(v_i_4639_, v___x_4649_);
lean_inc(v_sepStx_4648_);
v___x_4651_ = lean_array_push(v_acc_4643_, v_sepStx_4648_);
v___x_4652_ = lean_array_push(v___x_4651_, v_stx_4644_);
v___x_4653_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4640_, v_a_4641_, v_p_4642_, v___x_4650_, v___x_4652_);
return v___x_4653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4669_, lean_object* v_inst_4670_, lean_object* v_a_4671_, lean_object* v_p_4672_, lean_object* v_acc_4673_, lean_object* v_stx_4674_, lean_object* v_____do__lift_4675_){
_start:
{
uint8_t v_____do__lift_284__boxed_4676_; lean_object* v_res_4677_; 
v_____do__lift_284__boxed_4676_ = lean_unbox(v_____do__lift_4675_);
v_res_4677_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4669_, v_inst_4670_, v_a_4671_, v_p_4672_, v_acc_4673_, v_stx_4674_, v_____do__lift_284__boxed_4676_);
lean_dec(v_i_4669_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4678_, lean_object* v_a_4679_, lean_object* v_p_4680_, lean_object* v_i_4681_, lean_object* v_acc_4682_){
_start:
{
lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4683_ = lean_array_get_size(v_a_4679_);
v___x_4684_ = lean_nat_dec_lt(v_i_4681_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_object* v_toApplicative_4685_; lean_object* v_toPure_4686_; lean_object* v___x_4687_; 
lean_dec(v_i_4681_);
lean_dec(v_p_4680_);
lean_dec_ref(v_a_4679_);
v_toApplicative_4685_ = lean_ctor_get(v_inst_4678_, 0);
lean_inc_ref(v_toApplicative_4685_);
lean_dec_ref(v_inst_4678_);
v_toPure_4686_ = lean_ctor_get(v_toApplicative_4685_, 1);
lean_inc(v_toPure_4686_);
lean_dec_ref(v_toApplicative_4685_);
v___x_4687_ = lean_apply_2(v_toPure_4686_, lean_box(0), v_acc_4682_);
return v___x_4687_;
}
else
{
lean_object* v_toBind_4688_; lean_object* v_stx_4689_; lean_object* v___f_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_toBind_4688_ = lean_ctor_get(v_inst_4678_, 1);
lean_inc(v_toBind_4688_);
v_stx_4689_ = lean_array_fget(v_a_4679_, v_i_4681_);
lean_inc(v_stx_4689_);
lean_inc(v_p_4680_);
v___f_4690_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4690_, 0, v_i_4681_);
lean_closure_set(v___f_4690_, 1, v_inst_4678_);
lean_closure_set(v___f_4690_, 2, v_a_4679_);
lean_closure_set(v___f_4690_, 3, v_p_4680_);
lean_closure_set(v___f_4690_, 4, v_acc_4682_);
lean_closure_set(v___f_4690_, 5, v_stx_4689_);
v___x_4691_ = lean_apply_1(v_p_4680_, v_stx_4689_);
v___x_4692_ = lean_apply_4(v_toBind_4688_, lean_box(0), lean_box(0), v___x_4691_, v___f_4690_);
return v___x_4692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4693_, lean_object* v_inst_4694_, lean_object* v_a_4695_, lean_object* v_p_4696_, lean_object* v_i_4697_, lean_object* v_acc_4698_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4694_, v_a_4695_, v_p_4696_, v_i_4697_, v_acc_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4700_, lean_object* v_a_4701_, lean_object* v_p_4702_){
_start:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4703_ = lean_unsigned_to_nat(0u);
v___x_4704_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4705_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4700_, v_a_4701_, v_p_4702_, v___x_4703_, v___x_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4706_, lean_object* v_inst_4707_, lean_object* v_a_4708_, lean_object* v_p_4709_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Array_filterSepElemsM___redArg(v_inst_4707_, v_a_4708_, v_p_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4711_, lean_object* v_x_4712_){
_start:
{
lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4713_ = lean_apply_1(v_p_4711_, v_x_4712_);
v___x_4714_ = lean_unbox(v___x_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4715_, lean_object* v_x_4716_){
_start:
{
uint8_t v_res_4717_; lean_object* v_r_4718_; 
v_res_4717_ = l_Array_filterSepElems___lam__0(v_p_4715_, v_x_4716_);
v_r_4718_ = lean_box(v_res_4717_);
return v_r_4718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4719_, lean_object* v_p_4720_, lean_object* v_i_4721_, lean_object* v_acc_4722_){
_start:
{
lean_object* v___x_4723_; uint8_t v___x_4724_; 
v___x_4723_ = lean_array_get_size(v_a_4719_);
v___x_4724_ = lean_nat_dec_lt(v_i_4721_, v___x_4723_);
if (v___x_4724_ == 0)
{
lean_dec(v_i_4721_);
lean_dec_ref(v_p_4720_);
return v_acc_4722_;
}
else
{
lean_object* v_stx_4725_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v_stx_4725_ = lean_array_fget_borrowed(v_a_4719_, v_i_4721_);
lean_inc_ref(v_p_4720_);
lean_inc(v_stx_4725_);
v___x_4734_ = lean_apply_1(v_p_4720_, v_stx_4725_);
v___x_4735_ = lean_unbox(v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_unsigned_to_nat(2u);
v___x_4737_ = lean_nat_add(v_i_4721_, v___x_4736_);
lean_dec(v_i_4721_);
v_i_4721_ = v___x_4737_;
goto _start;
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; uint8_t v___x_4741_; 
v___x_4739_ = lean_array_get_size(v_acc_4722_);
v___x_4740_ = lean_unsigned_to_nat(0u);
v___x_4741_ = lean_nat_dec_eq(v___x_4739_, v___x_4740_);
if (v___x_4741_ == 0)
{
uint8_t v___x_4742_; 
v___x_4742_ = lean_nat_dec_eq(v_i_4721_, v___x_4740_);
if (v___x_4742_ == 0)
{
goto v___jp_4726_;
}
else
{
if (v___x_4741_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4743_ = lean_unsigned_to_nat(2u);
v___x_4744_ = lean_nat_add(v_i_4721_, v___x_4743_);
lean_dec(v_i_4721_);
lean_inc(v_stx_4725_);
v___x_4745_ = lean_array_push(v_acc_4722_, v_stx_4725_);
v_i_4721_ = v___x_4744_;
v_acc_4722_ = v___x_4745_;
goto _start;
}
else
{
goto v___jp_4726_;
}
}
}
else
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
v___x_4747_ = lean_unsigned_to_nat(2u);
v___x_4748_ = lean_nat_add(v_i_4721_, v___x_4747_);
lean_dec(v_i_4721_);
lean_inc(v_stx_4725_);
v___x_4749_ = lean_array_push(v_acc_4722_, v_stx_4725_);
v_i_4721_ = v___x_4748_;
v_acc_4722_ = v___x_4749_;
goto _start;
}
}
v___jp_4726_:
{
lean_object* v___x_4727_; lean_object* v_sepStx_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4727_ = lean_nat_pred(v_i_4721_);
v_sepStx_4728_ = lean_array_fget_borrowed(v_a_4719_, v___x_4727_);
lean_dec(v___x_4727_);
v___x_4729_ = lean_unsigned_to_nat(2u);
v___x_4730_ = lean_nat_add(v_i_4721_, v___x_4729_);
lean_dec(v_i_4721_);
lean_inc(v_sepStx_4728_);
v___x_4731_ = lean_array_push(v_acc_4722_, v_sepStx_4728_);
lean_inc(v_stx_4725_);
v___x_4732_ = lean_array_push(v___x_4731_, v_stx_4725_);
v_i_4721_ = v___x_4730_;
v_acc_4722_ = v___x_4732_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4751_, lean_object* v_p_4752_, lean_object* v_i_4753_, lean_object* v_acc_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4751_, v_p_4752_, v_i_4753_, v_acc_4754_);
lean_dec_ref(v_a_4751_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4756_, lean_object* v_p_4757_){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4758_ = lean_unsigned_to_nat(0u);
v___x_4759_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4760_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4756_, v_p_4757_, v___x_4758_, v___x_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4761_, lean_object* v_p_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4761_, v_p_4762_);
lean_dec_ref(v_a_4761_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4764_, lean_object* v_p_4765_){
_start:
{
lean_object* v___f_4766_; lean_object* v___x_4767_; 
v___f_4766_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4766_, 0, v_p_4765_);
v___x_4767_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4764_, v___f_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4768_, lean_object* v_p_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Array_filterSepElems(v_a_4768_, v_p_4769_);
lean_dec_ref(v_a_4768_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4771_, lean_object* v_acc_4772_, lean_object* v_inst_4773_, lean_object* v_a_4774_, lean_object* v_f_4775_, lean_object* v_stx_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4771_, v_acc_4772_, v_inst_4773_, v_a_4774_, v_f_4775_, v_stx_4776_);
lean_dec(v_i_4771_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4778_, lean_object* v_a_4779_, lean_object* v_f_4780_, lean_object* v_i_4781_, lean_object* v_acc_4782_){
_start:
{
lean_object* v___x_4783_; uint8_t v___x_4784_; 
v___x_4783_ = lean_array_get_size(v_a_4779_);
v___x_4784_ = lean_nat_dec_lt(v_i_4781_, v___x_4783_);
if (v___x_4784_ == 0)
{
lean_object* v_toApplicative_4785_; lean_object* v_toPure_4786_; lean_object* v___x_4787_; 
lean_dec(v_i_4781_);
lean_dec(v_f_4780_);
lean_dec_ref(v_a_4779_);
v_toApplicative_4785_ = lean_ctor_get(v_inst_4778_, 0);
lean_inc_ref(v_toApplicative_4785_);
lean_dec_ref(v_inst_4778_);
v_toPure_4786_ = lean_ctor_get(v_toApplicative_4785_, 1);
lean_inc(v_toPure_4786_);
lean_dec_ref(v_toApplicative_4785_);
v___x_4787_ = lean_apply_2(v_toPure_4786_, lean_box(0), v_acc_4782_);
return v___x_4787_;
}
else
{
lean_object* v_stx_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; uint8_t v___x_4792_; 
v_stx_4788_ = lean_array_fget_borrowed(v_a_4779_, v_i_4781_);
v___x_4789_ = lean_unsigned_to_nat(2u);
v___x_4790_ = lean_nat_mod(v_i_4781_, v___x_4789_);
v___x_4791_ = lean_unsigned_to_nat(0u);
v___x_4792_ = lean_nat_dec_eq(v___x_4790_, v___x_4791_);
lean_dec(v___x_4790_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4793_ = lean_unsigned_to_nat(1u);
v___x_4794_ = lean_nat_add(v_i_4781_, v___x_4793_);
lean_dec(v_i_4781_);
lean_inc(v_stx_4788_);
v___x_4795_ = lean_array_push(v_acc_4782_, v_stx_4788_);
v_i_4781_ = v___x_4794_;
v_acc_4782_ = v___x_4795_;
goto _start;
}
else
{
lean_object* v_toBind_4797_; lean_object* v___f_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
lean_inc(v_stx_4788_);
v_toBind_4797_ = lean_ctor_get(v_inst_4778_, 1);
lean_inc(v_toBind_4797_);
lean_inc(v_f_4780_);
v___f_4798_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4798_, 0, v_i_4781_);
lean_closure_set(v___f_4798_, 1, v_acc_4782_);
lean_closure_set(v___f_4798_, 2, v_inst_4778_);
lean_closure_set(v___f_4798_, 3, v_a_4779_);
lean_closure_set(v___f_4798_, 4, v_f_4780_);
v___x_4799_ = lean_apply_1(v_f_4780_, v_stx_4788_);
v___x_4800_ = lean_apply_4(v_toBind_4797_, lean_box(0), lean_box(0), v___x_4799_, v___f_4798_);
return v___x_4800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4801_, lean_object* v_acc_4802_, lean_object* v_inst_4803_, lean_object* v_a_4804_, lean_object* v_f_4805_, lean_object* v_stx_4806_){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4807_ = lean_unsigned_to_nat(1u);
v___x_4808_ = lean_nat_add(v_i_4801_, v___x_4807_);
v___x_4809_ = lean_array_push(v_acc_4802_, v_stx_4806_);
v___x_4810_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4803_, v_a_4804_, v_f_4805_, v___x_4808_, v___x_4809_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4811_, lean_object* v_inst_4812_, lean_object* v_a_4813_, lean_object* v_f_4814_, lean_object* v_i_4815_, lean_object* v_acc_4816_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4812_, v_a_4813_, v_f_4814_, v_i_4815_, v_acc_4816_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4818_, lean_object* v_a_4819_, lean_object* v_f_4820_){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = lean_unsigned_to_nat(0u);
v___x_4822_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4823_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4818_, v_a_4819_, v_f_4820_, v___x_4821_, v___x_4822_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4824_, lean_object* v_inst_4825_, lean_object* v_a_4826_, lean_object* v_f_4827_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Array_mapSepElemsM___redArg(v_inst_4825_, v_a_4826_, v_f_4827_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4829_, lean_object* v_x_4830_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_apply_1(v_f_4829_, v_x_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4832_, lean_object* v_f_4833_, lean_object* v_i_4834_, lean_object* v_acc_4835_){
_start:
{
lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4836_ = lean_array_get_size(v_a_4832_);
v___x_4837_ = lean_nat_dec_lt(v_i_4834_, v___x_4836_);
if (v___x_4837_ == 0)
{
lean_dec(v_i_4834_);
lean_dec_ref(v_f_4833_);
return v_acc_4835_;
}
else
{
lean_object* v_stx_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
v_stx_4838_ = lean_array_fget_borrowed(v_a_4832_, v_i_4834_);
v___x_4839_ = lean_unsigned_to_nat(2u);
v___x_4840_ = lean_nat_mod(v_i_4834_, v___x_4839_);
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = lean_nat_dec_eq(v___x_4840_, v___x_4841_);
lean_dec(v___x_4840_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4843_ = lean_unsigned_to_nat(1u);
v___x_4844_ = lean_nat_add(v_i_4834_, v___x_4843_);
lean_dec(v_i_4834_);
lean_inc(v_stx_4838_);
v___x_4845_ = lean_array_push(v_acc_4835_, v_stx_4838_);
v_i_4834_ = v___x_4844_;
v_acc_4835_ = v___x_4845_;
goto _start;
}
else
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_inc_ref(v_f_4833_);
lean_inc(v_stx_4838_);
v___x_4847_ = lean_apply_1(v_f_4833_, v_stx_4838_);
v___x_4848_ = lean_unsigned_to_nat(1u);
v___x_4849_ = lean_nat_add(v_i_4834_, v___x_4848_);
lean_dec(v_i_4834_);
v___x_4850_ = lean_array_push(v_acc_4835_, v___x_4847_);
v_i_4834_ = v___x_4849_;
v_acc_4835_ = v___x_4850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4852_, lean_object* v_f_4853_, lean_object* v_i_4854_, lean_object* v_acc_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4852_, v_f_4853_, v_i_4854_, v_acc_4855_);
lean_dec_ref(v_a_4852_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4857_, lean_object* v_f_4858_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4861_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4857_, v_f_4858_, v___x_4859_, v___x_4860_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4862_, lean_object* v_f_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4862_, v_f_4863_);
lean_dec_ref(v_a_4862_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4865_, lean_object* v_f_4866_){
_start:
{
lean_object* v___f_4867_; lean_object* v___x_4868_; 
v___f_4867_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4867_, 0, v_f_4866_);
v___x_4868_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4865_, v___f_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4869_, lean_object* v_f_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Array_mapSepElems(v_a_4869_, v_f_4870_);
lean_dec_ref(v_a_4869_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4872_, size_t v_i_4873_, size_t v_stop_4874_, lean_object* v_b_4875_){
_start:
{
lean_object* v___y_4877_; uint8_t v___x_4881_; 
v___x_4881_ = lean_usize_dec_eq(v_i_4873_, v_stop_4874_);
if (v___x_4881_ == 0)
{
lean_object* v_fst_4882_; uint8_t v___x_4883_; 
v_fst_4882_ = lean_ctor_get(v_b_4875_, 0);
v___x_4883_ = lean_unbox(v_fst_4882_);
if (v___x_4883_ == 0)
{
lean_object* v_snd_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4893_; 
v_snd_4884_ = lean_ctor_get(v_b_4875_, 1);
v_isSharedCheck_4893_ = !lean_is_exclusive(v_b_4875_);
if (v_isSharedCheck_4893_ == 0)
{
lean_object* v_unused_4894_; 
v_unused_4894_ = lean_ctor_get(v_b_4875_, 0);
lean_dec(v_unused_4894_);
v___x_4886_ = v_b_4875_;
v_isShared_4887_ = v_isSharedCheck_4893_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_snd_4884_);
lean_dec(v_b_4875_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4893_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
uint8_t v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4888_ = 1;
v___x_4889_ = lean_box(v___x_4888_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v___x_4889_);
v___x_4891_ = v___x_4886_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_snd_4884_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
v___y_4877_ = v___x_4891_;
goto v___jp_4876_;
}
}
}
else
{
lean_object* v_snd_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4905_; 
v_snd_4895_ = lean_ctor_get(v_b_4875_, 1);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_b_4875_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; 
v_unused_4906_ = lean_ctor_get(v_b_4875_, 0);
lean_dec(v_unused_4906_);
v___x_4897_ = v_b_4875_;
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_snd_4895_);
lean_dec(v_b_4875_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4903_; 
v___x_4899_ = lean_array_uget_borrowed(v_as_4872_, v_i_4873_);
lean_inc(v___x_4899_);
v___x_4900_ = lean_array_push(v_snd_4895_, v___x_4899_);
v___x_4901_ = lean_box(v___x_4881_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 1, v___x_4900_);
lean_ctor_set(v___x_4897_, 0, v___x_4901_);
v___x_4903_ = v___x_4897_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v___x_4900_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
v___y_4877_ = v___x_4903_;
goto v___jp_4876_;
}
}
}
}
else
{
return v_b_4875_;
}
v___jp_4876_:
{
size_t v___x_4878_; size_t v___x_4879_; 
v___x_4878_ = ((size_t)1ULL);
v___x_4879_ = lean_usize_add(v_i_4873_, v___x_4878_);
v_i_4873_ = v___x_4879_;
v_b_4875_ = v___y_4877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4907_, lean_object* v_i_4908_, lean_object* v_stop_4909_, lean_object* v_b_4910_){
_start:
{
size_t v_i_boxed_4911_; size_t v_stop_boxed_4912_; lean_object* v_res_4913_; 
v_i_boxed_4911_ = lean_unbox_usize(v_i_4908_);
lean_dec(v_i_4908_);
v_stop_boxed_4912_ = lean_unbox_usize(v_stop_4909_);
lean_dec(v_stop_4909_);
v_res_4913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4907_, v_i_boxed_4911_, v_stop_boxed_4912_, v_b_4910_);
lean_dec_ref(v_as_4907_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4914_){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; 
v___x_4915_ = lean_unsigned_to_nat(0u);
v___x_4916_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4917_ = lean_array_get_size(v_sa_4914_);
v___x_4918_ = lean_nat_dec_lt(v___x_4915_, v___x_4917_);
if (v___x_4918_ == 0)
{
return v___x_4916_;
}
else
{
lean_object* v___x_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4919_ = lean_box(v___x_4918_);
v___x_4920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
lean_ctor_set(v___x_4920_, 1, v___x_4916_);
v___x_4921_ = lean_nat_dec_le(v___x_4917_, v___x_4917_);
if (v___x_4921_ == 0)
{
if (v___x_4918_ == 0)
{
lean_dec_ref_known(v___x_4920_, 2);
return v___x_4916_;
}
else
{
size_t v___x_4922_; size_t v___x_4923_; lean_object* v___x_4924_; lean_object* v_snd_4925_; 
v___x_4922_ = ((size_t)0ULL);
v___x_4923_ = lean_usize_of_nat(v___x_4917_);
v___x_4924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4914_, v___x_4922_, v___x_4923_, v___x_4920_);
v_snd_4925_ = lean_ctor_get(v___x_4924_, 1);
lean_inc(v_snd_4925_);
lean_dec_ref(v___x_4924_);
return v_snd_4925_;
}
}
else
{
size_t v___x_4926_; size_t v___x_4927_; lean_object* v___x_4928_; lean_object* v_snd_4929_; 
v___x_4926_ = ((size_t)0ULL);
v___x_4927_ = lean_usize_of_nat(v___x_4917_);
v___x_4928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4914_, v___x_4926_, v___x_4927_, v___x_4920_);
v_snd_4929_ = lean_ctor_get(v___x_4928_, 1);
lean_inc(v_snd_4929_);
lean_dec_ref(v___x_4928_);
return v_snd_4929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4930_);
lean_dec_ref(v_sa_4930_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4932_, lean_object* v_sa_4933_){
_start:
{
lean_object* v___x_4934_; 
v___x_4934_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4933_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4935_, lean_object* v_sa_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Syntax_SepArray_getElems(v_sep_4935_, v_sa_4936_);
lean_dec_ref(v_sa_4936_);
lean_dec_ref(v_sep_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4938_){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4939_ = lean_unsigned_to_nat(0u);
v___x_4940_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4941_ = lean_array_get_size(v_sa_4938_);
v___x_4942_ = lean_nat_dec_lt(v___x_4939_, v___x_4941_);
if (v___x_4942_ == 0)
{
return v___x_4940_;
}
else
{
lean_object* v___x_4943_; lean_object* v___x_4944_; uint8_t v___x_4945_; 
v___x_4943_ = lean_box(v___x_4942_);
v___x_4944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v___x_4940_);
v___x_4945_ = lean_nat_dec_le(v___x_4941_, v___x_4941_);
if (v___x_4945_ == 0)
{
if (v___x_4942_ == 0)
{
lean_dec_ref_known(v___x_4944_, 2);
return v___x_4940_;
}
else
{
size_t v___x_4946_; size_t v___x_4947_; lean_object* v___x_4948_; lean_object* v_snd_4949_; 
v___x_4946_ = ((size_t)0ULL);
v___x_4947_ = lean_usize_of_nat(v___x_4941_);
v___x_4948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4938_, v___x_4946_, v___x_4947_, v___x_4944_);
v_snd_4949_ = lean_ctor_get(v___x_4948_, 1);
lean_inc(v_snd_4949_);
lean_dec_ref(v___x_4948_);
return v_snd_4949_;
}
}
else
{
size_t v___x_4950_; size_t v___x_4951_; lean_object* v___x_4952_; lean_object* v_snd_4953_; 
v___x_4950_ = ((size_t)0ULL);
v___x_4951_ = lean_usize_of_nat(v___x_4941_);
v___x_4952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4938_, v___x_4950_, v___x_4951_, v___x_4944_);
v_snd_4953_ = lean_ctor_get(v___x_4952_, 1);
lean_inc(v_snd_4953_);
lean_dec_ref(v___x_4952_);
return v_snd_4953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4954_);
lean_dec_ref(v_sa_4954_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4956_, lean_object* v_sep_4957_, lean_object* v_sa_4958_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4960_, lean_object* v_sep_4961_, lean_object* v_sa_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Syntax_TSepArray_getElems(v_k_4960_, v_sep_4961_, v_sa_4962_);
lean_dec_ref(v_sa_4962_);
lean_dec_ref(v_sep_4961_);
lean_dec(v_k_4960_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4964_, lean_object* v_sa_4965_, lean_object* v_e_4966_){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; uint8_t v___x_4969_; 
v___x_4967_ = lean_array_get_size(v_sa_4965_);
v___x_4968_ = lean_unsigned_to_nat(0u);
v___x_4969_ = lean_nat_dec_eq(v___x_4967_, v___x_4968_);
if (v___x_4969_ == 0)
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4970_ = l_Lean_mkAtom(v_sep_4964_);
v___x_4971_ = lean_array_push(v_sa_4965_, v___x_4970_);
v___x_4972_ = lean_array_push(v___x_4971_, v_e_4966_);
return v___x_4972_;
}
else
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_dec_ref(v_sa_4965_);
lean_dec_ref(v_sep_4964_);
v___x_4973_ = lean_unsigned_to_nat(1u);
v___x_4974_ = lean_mk_empty_array_with_capacity(v___x_4973_);
v___x_4975_ = lean_array_push(v___x_4974_, v_e_4966_);
return v___x_4975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4976_, lean_object* v_sep_4977_, lean_object* v_sa_4978_, lean_object* v_e_4979_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4977_, v_sa_4978_, v_e_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4981_, lean_object* v_sep_4982_, lean_object* v_sa_4983_, lean_object* v_e_4984_){
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l_Lean_Syntax_TSepArray_push(v_k_4981_, v_sep_4982_, v_sa_4983_, v_e_4984_);
lean_dec(v_k_4981_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4986_){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4988_);
lean_dec_ref(v_sep_4988_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4990_, lean_object* v_k_4991_){
_start:
{
lean_object* v___x_4992_; 
v___x_4992_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4993_, lean_object* v_k_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4993_, v_k_4994_);
lean_dec_ref(v_k_4994_);
lean_dec(v_sep_4993_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object* v_sep_4996_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___boxed), 2, 1);
lean_closure_set(v___x_4997_, 0, v_sep_4996_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4998_, lean_object* v_sep_4999_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_5000_, 0, v_k_4998_);
lean_closure_set(v___x_5000_, 1, v_sep_4999_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_5001_, lean_object* v_x_5002_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_apply_1(v_inst_5001_, v_x_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v___x_5006_; size_t v_sz_5007_; size_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5006_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5007_ = lean_array_size(v_a_5005_);
v___x_5008_ = ((size_t)0ULL);
v___x_5009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5006_, v___f_5004_, v_sz_5007_, v___x_5008_, v_a_5005_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5010_){
_start:
{
lean_object* v___f_5011_; lean_object* v___f_5012_; 
v___f_5011_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5011_, 0, v_inst_5010_);
v___f_5012_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5012_, 0, v___f_5011_);
return v___f_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5013_, lean_object* v_k_x27_5014_, lean_object* v_inst_5015_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5015_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5017_, lean_object* v_k_x27_5018_, lean_object* v_inst_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5017_, v_k_x27_5018_, v_inst_5019_);
lean_dec(v_k_x27_5018_);
lean_dec(v_k_5017_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object* v_a_5021_){
_start:
{
lean_inc_ref(v_a_5021_);
return v_a_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object* v_a_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(v_a_5022_);
lean_dec_ref(v_a_5022_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5025_){
_start:
{
lean_object* v___f_5026_; 
v___f_5026_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5036_){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5037_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_5038_ = lean_box(2);
v___x_5039_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5040_ = lean_unsigned_to_nat(2u);
v___x_5041_ = lean_mk_empty_array_with_capacity(v___x_5040_);
v___x_5042_ = lean_array_push(v___x_5041_, v_id_5036_);
v___x_5043_ = lean_array_push(v___x_5042_, v___x_5039_);
v___x_5044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5038_);
lean_ctor_set(v___x_5044_, 1, v___x_5037_);
lean_ctor_set(v___x_5044_, 2, v___x_5043_);
return v___x_5044_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = 123;
v___x_5049_ = lean_box_uint32(v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5050_, lean_object* v_i_5051_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Syntax_decodeQuotedChar(v_s_5050_, v_i_5051_);
if (lean_obj_tag(v___x_5052_) == 0)
{
uint32_t v_c_5053_; uint32_t v___x_5054_; uint8_t v___x_5055_; 
v_c_5053_ = lean_string_utf8_get(v_s_5050_, v_i_5051_);
v___x_5054_ = 123;
v___x_5055_ = lean_uint32_dec_eq(v_c_5053_, v___x_5054_);
if (v___x_5055_ == 0)
{
return v___x_5052_;
}
else
{
lean_object* v_i_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v_i_5056_ = lean_string_utf8_next(v_s_5050_, v_i_5051_);
v___x_5057_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
lean_ctor_set(v___x_5058_, 1, v_i_5056_);
v___x_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
return v___x_5059_;
}
}
else
{
return v___x_5052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5060_, lean_object* v_i_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5060_, v_i_5061_);
lean_dec(v_i_5061_);
lean_dec_ref(v_s_5060_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5063_, lean_object* v_i_5064_, lean_object* v_acc_5065_){
_start:
{
uint32_t v_c_5066_; lean_object* v_i_5067_; uint8_t v___y_5069_; uint32_t v___x_5088_; uint8_t v___x_5089_; 
v_c_5066_ = lean_string_utf8_get(v_s_5063_, v_i_5064_);
v_i_5067_ = lean_string_utf8_next(v_s_5063_, v_i_5064_);
lean_dec(v_i_5064_);
v___x_5088_ = 34;
v___x_5089_ = lean_uint32_dec_eq(v_c_5066_, v___x_5088_);
if (v___x_5089_ == 0)
{
uint32_t v___x_5090_; uint8_t v___x_5091_; 
v___x_5090_ = 123;
v___x_5091_ = lean_uint32_dec_eq(v_c_5066_, v___x_5090_);
v___y_5069_ = v___x_5091_;
goto v___jp_5068_;
}
else
{
v___y_5069_ = v___x_5089_;
goto v___jp_5068_;
}
v___jp_5068_:
{
if (v___y_5069_ == 0)
{
uint8_t v___x_5070_; 
v___x_5070_ = lean_string_utf8_at_end(v_s_5063_, v_i_5067_);
if (v___x_5070_ == 0)
{
uint32_t v___x_5071_; uint8_t v___x_5072_; 
v___x_5071_ = 92;
v___x_5072_ = lean_uint32_dec_eq(v_c_5066_, v___x_5071_);
if (v___x_5072_ == 0)
{
lean_object* v___x_5073_; 
v___x_5073_ = lean_string_push(v_acc_5065_, v_c_5066_);
v_i_5064_ = v_i_5067_;
v_acc_5065_ = v___x_5073_;
goto _start;
}
else
{
lean_object* v___x_5075_; 
v___x_5075_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5063_, v_i_5067_);
if (lean_obj_tag(v___x_5075_) == 1)
{
lean_object* v_val_5076_; lean_object* v_fst_5077_; lean_object* v_snd_5078_; uint32_t v___x_5079_; lean_object* v___x_5080_; 
lean_dec(v_i_5067_);
v_val_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_val_5076_);
lean_dec_ref_known(v___x_5075_, 1);
v_fst_5077_ = lean_ctor_get(v_val_5076_, 0);
lean_inc(v_fst_5077_);
v_snd_5078_ = lean_ctor_get(v_val_5076_, 1);
lean_inc(v_snd_5078_);
lean_dec(v_val_5076_);
v___x_5079_ = lean_unbox_uint32(v_fst_5077_);
lean_dec(v_fst_5077_);
v___x_5080_ = lean_string_push(v_acc_5065_, v___x_5079_);
v_i_5064_ = v_snd_5078_;
v_acc_5065_ = v___x_5080_;
goto _start;
}
else
{
lean_object* v___x_5082_; 
lean_dec(v___x_5075_);
lean_inc_ref(v_s_5063_);
v___x_5082_ = l_Lean_Syntax_decodeStringGap(v_s_5063_, v_i_5067_);
lean_dec(v_i_5067_);
if (lean_obj_tag(v___x_5082_) == 1)
{
lean_object* v_val_5083_; 
v_val_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_val_5083_);
lean_dec_ref_known(v___x_5082_, 1);
v_i_5064_ = v_val_5083_;
goto _start;
}
else
{
lean_object* v___x_5085_; 
lean_dec(v___x_5082_);
lean_dec_ref(v_acc_5065_);
lean_dec_ref(v_s_5063_);
v___x_5085_ = lean_box(0);
return v___x_5085_;
}
}
}
}
else
{
lean_object* v___x_5086_; 
lean_dec(v_i_5067_);
lean_dec_ref(v_acc_5065_);
lean_dec_ref(v_s_5063_);
v___x_5086_ = lean_box(0);
return v___x_5086_;
}
}
else
{
lean_object* v___x_5087_; 
lean_dec(v_i_5067_);
lean_dec_ref(v_s_5063_);
v___x_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5087_, 0, v_acc_5065_);
return v___x_5087_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5092_){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5093_ = lean_unsigned_to_nat(1u);
v___x_5094_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5095_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5092_, v___x_5093_, v___x_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5099_){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5100_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5101_ = l_Lean_Syntax_isLit_x3f(v___x_5100_, v_stx_5099_);
if (lean_obj_tag(v___x_5101_) == 0)
{
return v___x_5101_;
}
else
{
lean_object* v_val_5102_; lean_object* v___x_5103_; 
v_val_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_val_5102_);
lean_dec_ref_known(v___x_5101_, 1);
v___x_5103_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5102_);
return v___x_5103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5104_);
lean_dec(v_stx_5104_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5106_){
_start:
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; 
v___x_5107_ = l_Lean_Syntax_getArgs(v_stx_5106_);
v___x_5108_ = lean_unsigned_to_nat(0u);
v___x_5109_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5110_ = lean_array_get_size(v___x_5107_);
v___x_5111_ = lean_nat_dec_lt(v___x_5108_, v___x_5110_);
if (v___x_5111_ == 0)
{
lean_dec_ref(v___x_5107_);
return v___x_5109_;
}
else
{
lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; 
v___x_5112_ = lean_box(v___x_5111_);
v___x_5113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5113_, 0, v___x_5112_);
lean_ctor_set(v___x_5113_, 1, v___x_5109_);
v___x_5114_ = lean_nat_dec_le(v___x_5110_, v___x_5110_);
if (v___x_5114_ == 0)
{
if (v___x_5111_ == 0)
{
lean_dec_ref_known(v___x_5113_, 2);
lean_dec_ref(v___x_5107_);
return v___x_5109_;
}
else
{
size_t v___x_5115_; size_t v___x_5116_; lean_object* v___x_5117_; lean_object* v_snd_5118_; 
v___x_5115_ = ((size_t)0ULL);
v___x_5116_ = lean_usize_of_nat(v___x_5110_);
v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5107_, v___x_5115_, v___x_5116_, v___x_5113_);
lean_dec_ref(v___x_5107_);
v_snd_5118_ = lean_ctor_get(v___x_5117_, 1);
lean_inc(v_snd_5118_);
lean_dec_ref(v___x_5117_);
return v_snd_5118_;
}
}
else
{
size_t v___x_5119_; size_t v___x_5120_; lean_object* v___x_5121_; lean_object* v_snd_5122_; 
v___x_5119_ = ((size_t)0ULL);
v___x_5120_ = lean_usize_of_nat(v___x_5110_);
v___x_5121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5107_, v___x_5119_, v___x_5120_, v___x_5113_);
lean_dec_ref(v___x_5107_);
v_snd_5122_ = lean_ctor_get(v___x_5121_, 1);
lean_inc(v_snd_5122_);
lean_dec_ref(v___x_5121_);
return v_snd_5122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Syntax_getSepArgs(v_stx_5123_);
lean_dec(v_stx_5123_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5125_, lean_object* v_mkElem_5126_, lean_object* v_mkLit_5127_, lean_object* v_as_5128_, size_t v_sz_5129_, size_t v_i_5130_, lean_object* v_b_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_a_5135_; lean_object* v_a_5136_; lean_object* v_elem_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; uint8_t v___x_5148_; 
v___x_5148_ = lean_usize_dec_lt(v_i_5130_, v_sz_5129_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; 
lean_dec_ref(v_mkLit_5127_);
lean_dec_ref(v_mkElem_5126_);
lean_dec_ref(v_mkAppend_5125_);
v___x_5149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5149_, 0, v_b_5131_);
lean_ctor_set(v___x_5149_, 1, v___y_5133_);
return v___x_5149_;
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5151_; 
v_a_5150_ = lean_array_uget_borrowed(v_as_5128_, v_i_5130_);
v___x_5151_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5150_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_methods_5152_; lean_object* v_quotContext_5153_; lean_object* v_currMacroScope_5154_; lean_object* v_currRecDepth_5155_; lean_object* v_maxRecDepth_5156_; lean_object* v_ref_5157_; lean_object* v_ref_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
v_methods_5152_ = lean_ctor_get(v___y_5132_, 0);
v_quotContext_5153_ = lean_ctor_get(v___y_5132_, 1);
v_currMacroScope_5154_ = lean_ctor_get(v___y_5132_, 2);
v_currRecDepth_5155_ = lean_ctor_get(v___y_5132_, 3);
v_maxRecDepth_5156_ = lean_ctor_get(v___y_5132_, 4);
v_ref_5157_ = lean_ctor_get(v___y_5132_, 5);
v_ref_5158_ = l_Lean_replaceRef(v_a_5150_, v_ref_5157_);
lean_inc(v_maxRecDepth_5156_);
lean_inc(v_currRecDepth_5155_);
lean_inc(v_currMacroScope_5154_);
lean_inc(v_quotContext_5153_);
lean_inc(v_methods_5152_);
v___x_5159_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5159_, 0, v_methods_5152_);
lean_ctor_set(v___x_5159_, 1, v_quotContext_5153_);
lean_ctor_set(v___x_5159_, 2, v_currMacroScope_5154_);
lean_ctor_set(v___x_5159_, 3, v_currRecDepth_5155_);
lean_ctor_set(v___x_5159_, 4, v_maxRecDepth_5156_);
lean_ctor_set(v___x_5159_, 5, v_ref_5158_);
lean_inc_ref(v_mkElem_5126_);
lean_inc(v_a_5150_);
v___x_5160_ = lean_apply_3(v_mkElem_5126_, v_a_5150_, v___x_5159_, v___y_5133_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v_a_5161_; lean_object* v_a_5162_; 
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
lean_inc(v_a_5161_);
v_a_5162_ = lean_ctor_get(v___x_5160_, 1);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5160_, 2);
v_elem_5141_ = v_a_5161_;
v___y_5142_ = v___y_5132_;
v___y_5143_ = v_a_5162_;
goto v___jp_5140_;
}
else
{
lean_dec(v_b_5131_);
lean_dec_ref(v_mkLit_5127_);
lean_dec_ref(v_mkElem_5126_);
lean_dec_ref(v_mkAppend_5125_);
return v___x_5160_;
}
}
else
{
lean_object* v_val_5163_; uint8_t v___x_5164_; 
v_val_5163_ = lean_ctor_get(v___x_5151_, 0);
lean_inc_n(v_val_5163_, 2);
lean_dec_ref_known(v___x_5151_, 1);
v___x_5164_ = lean_string_isempty(v_val_5163_);
if (v___x_5164_ == 0)
{
lean_object* v_methods_5165_; lean_object* v_quotContext_5166_; lean_object* v_currMacroScope_5167_; lean_object* v_currRecDepth_5168_; lean_object* v_maxRecDepth_5169_; lean_object* v_ref_5170_; lean_object* v_ref_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
v_methods_5165_ = lean_ctor_get(v___y_5132_, 0);
v_quotContext_5166_ = lean_ctor_get(v___y_5132_, 1);
v_currMacroScope_5167_ = lean_ctor_get(v___y_5132_, 2);
v_currRecDepth_5168_ = lean_ctor_get(v___y_5132_, 3);
v_maxRecDepth_5169_ = lean_ctor_get(v___y_5132_, 4);
v_ref_5170_ = lean_ctor_get(v___y_5132_, 5);
v_ref_5171_ = l_Lean_replaceRef(v_a_5150_, v_ref_5170_);
lean_inc(v_maxRecDepth_5169_);
lean_inc(v_currRecDepth_5168_);
lean_inc(v_currMacroScope_5167_);
lean_inc(v_quotContext_5166_);
lean_inc(v_methods_5165_);
v___x_5172_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5172_, 0, v_methods_5165_);
lean_ctor_set(v___x_5172_, 1, v_quotContext_5166_);
lean_ctor_set(v___x_5172_, 2, v_currMacroScope_5167_);
lean_ctor_set(v___x_5172_, 3, v_currRecDepth_5168_);
lean_ctor_set(v___x_5172_, 4, v_maxRecDepth_5169_);
lean_ctor_set(v___x_5172_, 5, v_ref_5171_);
lean_inc_ref(v_mkLit_5127_);
v___x_5173_ = lean_apply_3(v_mkLit_5127_, v_val_5163_, v___x_5172_, v___y_5133_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; lean_object* v_a_5175_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_a_5174_);
v_a_5175_ = lean_ctor_get(v___x_5173_, 1);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___x_5173_, 2);
v_elem_5141_ = v_a_5174_;
v___y_5142_ = v___y_5132_;
v___y_5143_ = v_a_5175_;
goto v___jp_5140_;
}
else
{
lean_dec(v_b_5131_);
lean_dec_ref(v_mkLit_5127_);
lean_dec_ref(v_mkElem_5126_);
lean_dec_ref(v_mkAppend_5125_);
return v___x_5173_;
}
}
else
{
lean_dec(v_val_5163_);
v_a_5135_ = v_b_5131_;
v_a_5136_ = v___y_5133_;
goto v___jp_5134_;
}
}
}
v___jp_5134_:
{
size_t v___x_5137_; size_t v___x_5138_; 
v___x_5137_ = ((size_t)1ULL);
v___x_5138_ = lean_usize_add(v_i_5130_, v___x_5137_);
v_i_5130_ = v___x_5138_;
v_b_5131_ = v_a_5135_;
v___y_5133_ = v_a_5136_;
goto _start;
}
v___jp_5140_:
{
uint8_t v___x_5144_; 
v___x_5144_ = l_Lean_Syntax_isMissing(v_b_5131_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; 
lean_inc_ref(v_mkAppend_5125_);
lean_inc_ref(v___y_5142_);
v___x_5145_ = lean_apply_4(v_mkAppend_5125_, v_b_5131_, v_elem_5141_, v___y_5142_, v___y_5143_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v_a_5147_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
v_a_5147_ = lean_ctor_get(v___x_5145_, 1);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5145_, 2);
v_a_5135_ = v_a_5146_;
v_a_5136_ = v_a_5147_;
goto v___jp_5134_;
}
else
{
lean_dec_ref(v_mkLit_5127_);
lean_dec_ref(v_mkElem_5126_);
lean_dec_ref(v_mkAppend_5125_);
return v___x_5145_;
}
}
else
{
lean_dec(v_b_5131_);
v_a_5135_ = v_elem_5141_;
v_a_5136_ = v___y_5143_;
goto v___jp_5134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5176_, lean_object* v_mkElem_5177_, lean_object* v_mkLit_5178_, lean_object* v_as_5179_, lean_object* v_sz_5180_, lean_object* v_i_5181_, lean_object* v_b_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
size_t v_sz_boxed_5185_; size_t v_i_boxed_5186_; lean_object* v_res_5187_; 
v_sz_boxed_5185_ = lean_unbox_usize(v_sz_5180_);
lean_dec(v_sz_5180_);
v_i_boxed_5186_ = lean_unbox_usize(v_i_5181_);
lean_dec(v_i_5181_);
v_res_5187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5176_, v_mkElem_5177_, v_mkLit_5178_, v_as_5179_, v_sz_boxed_5185_, v_i_boxed_5186_, v_b_5182_, v___y_5183_, v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec_ref(v_as_5179_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5188_, lean_object* v_mkAppend_5189_, lean_object* v_mkElem_5190_, lean_object* v_mkLit_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_result_5194_; size_t v_sz_5195_; size_t v___x_5196_; lean_object* v___x_5197_; 
v_result_5194_ = lean_box(0);
v_sz_5195_ = lean_array_size(v_chunks_5188_);
v___x_5196_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5191_);
v___x_5197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5189_, v_mkElem_5190_, v_mkLit_5191_, v_chunks_5188_, v_sz_5195_, v___x_5196_, v_result_5194_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v_a_5199_; uint8_t v___x_5200_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
v_a_5199_ = lean_ctor_get(v___x_5197_, 1);
lean_inc(v_a_5199_);
v___x_5200_ = l_Lean_Syntax_isMissing(v_a_5198_);
lean_dec(v_a_5198_);
if (v___x_5200_ == 0)
{
lean_dec(v_a_5199_);
lean_dec_ref(v_mkLit_5191_);
return v___x_5197_;
}
else
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
lean_dec_ref_known(v___x_5197_, 2);
v___x_5201_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5192_);
v___x_5202_ = lean_apply_3(v_mkLit_5191_, v___x_5201_, v_a_5192_, v_a_5199_);
return v___x_5202_;
}
}
else
{
lean_dec_ref(v_mkLit_5191_);
return v___x_5197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5203_, lean_object* v_mkAppend_5204_, lean_object* v_mkElem_5205_, lean_object* v_mkLit_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5203_, v_mkAppend_5204_, v_mkElem_5205_, v_mkLit_5206_, v_a_5207_, v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec_ref(v_chunks_5203_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5214_, lean_object* v_b_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v_ref_5218_; uint8_t v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v_ref_5218_ = lean_ctor_get(v___y_5216_, 5);
v___x_5219_ = 0;
v___x_5220_ = l_Lean_SourceInfo_fromRef(v_ref_5218_, v___x_5219_);
v___x_5221_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5222_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5220_);
v___x_5223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5220_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
v___x_5224_ = l_Lean_Syntax_node3(v___x_5220_, v___x_5221_, v_a_5214_, v___x_5223_, v_b_5215_);
v___x_5225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5224_);
lean_ctor_set(v___x_5225_, 1, v___y_5217_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5226_, lean_object* v_b_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5226_, v_b_5227_, v___y_5228_, v___y_5229_);
lean_dec_ref(v___y_5228_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5231_, lean_object* v_a_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_ref_5235_; uint8_t v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v_ref_5235_ = lean_ctor_get(v___y_5233_, 5);
v___x_5236_ = 0;
v___x_5237_ = l_Lean_SourceInfo_fromRef(v_ref_5235_, v___x_5236_);
v___x_5238_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5239_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5237_);
v___x_5240_ = l_Lean_Syntax_node1(v___x_5237_, v___x_5239_, v_a_5232_);
v___x_5241_ = l_Lean_Syntax_node2(v___x_5237_, v___x_5238_, v_ofInterpFn_5231_, v___x_5240_);
v___x_5242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5241_);
lean_ctor_set(v___x_5242_, 1, v___y_5234_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5243_, lean_object* v_a_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
lean_object* v_res_5247_; 
v_res_5247_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5243_, v_a_5244_, v___y_5245_, v___y_5246_);
lean_dec_ref(v___y_5245_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5248_, lean_object* v_s_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_ref_5252_; uint8_t v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
v_ref_5252_ = lean_ctor_get(v___y_5250_, 5);
v___x_5253_ = 0;
v___x_5254_ = l_Lean_SourceInfo_fromRef(v_ref_5252_, v___x_5253_);
v___x_5255_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5256_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5257_ = lean_box(2);
v___x_5258_ = l_Lean_Syntax_mkStrLit(v_s_5249_, v___x_5257_);
lean_inc(v___x_5254_);
v___x_5259_ = l_Lean_Syntax_node1(v___x_5254_, v___x_5256_, v___x_5258_);
v___x_5260_ = l_Lean_Syntax_node2(v___x_5254_, v___x_5255_, v_ofLitFn_5248_, v___x_5259_);
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
lean_ctor_set(v___x_5261_, 1, v___y_5251_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5262_, lean_object* v_s_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5262_, v_s_5263_, v___y_5264_, v___y_5265_);
lean_dec_ref(v___y_5264_);
return v_res_5266_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5284_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5285_ = l_String_toRawSubstring_x27(v___x_5284_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5306_, lean_object* v_type_5307_, lean_object* v_ofInterpFn_5308_, lean_object* v_ofLitFn_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_){
_start:
{
lean_object* v___f_5312_; lean_object* v___f_5313_; lean_object* v___f_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___f_5312_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5313_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5313_, 0, v_ofInterpFn_5308_);
v___f_5314_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5314_, 0, v_ofLitFn_5309_);
v___x_5315_ = l_Lean_Syntax_getArgs(v_interpStr_5306_);
v___x_5316_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5315_, v___f_5312_, v___f_5313_, v___f_5314_, v_a_5310_, v_a_5311_);
lean_dec_ref(v___x_5315_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5349_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
v_a_5318_ = lean_ctor_get(v___x_5316_, 1);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5320_ = v___x_5316_;
v_isShared_5321_ = v_isSharedCheck_5349_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_inc(v_a_5317_);
lean_dec(v___x_5316_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5349_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v_quotContext_5322_; lean_object* v_currMacroScope_5323_; lean_object* v_ref_5324_; uint8_t v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5347_; 
v_quotContext_5322_ = lean_ctor_get(v_a_5310_, 1);
v_currMacroScope_5323_ = lean_ctor_get(v_a_5310_, 2);
v_ref_5324_ = lean_ctor_get(v_a_5310_, 5);
v___x_5325_ = 0;
v___x_5326_ = l_Lean_SourceInfo_fromRef(v_ref_5324_, v___x_5325_);
v___x_5327_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5328_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5329_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5326_, 7);
v___x_5330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5326_);
lean_ctor_set(v___x_5330_, 1, v___x_5329_);
v___x_5331_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5332_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5333_ = lean_box(0);
lean_inc(v_currMacroScope_5323_);
lean_inc(v_quotContext_5322_);
v___x_5334_ = l_Lean_addMacroScope(v_quotContext_5322_, v___x_5333_, v_currMacroScope_5323_);
v___x_5335_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5326_);
lean_ctor_set(v___x_5336_, 1, v___x_5332_);
lean_ctor_set(v___x_5336_, 2, v___x_5334_);
lean_ctor_set(v___x_5336_, 3, v___x_5335_);
v___x_5337_ = l_Lean_Syntax_node1(v___x_5326_, v___x_5331_, v___x_5336_);
v___x_5338_ = l_Lean_Syntax_node2(v___x_5326_, v___x_5328_, v___x_5330_, v___x_5337_);
v___x_5339_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5326_);
lean_ctor_set(v___x_5340_, 1, v___x_5339_);
v___x_5341_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5342_ = l_Lean_Syntax_node1(v___x_5326_, v___x_5341_, v_type_5307_);
v___x_5343_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5344_, 0, v___x_5326_);
lean_ctor_set(v___x_5344_, 1, v___x_5343_);
v___x_5345_ = l_Lean_Syntax_node5(v___x_5326_, v___x_5327_, v___x_5338_, v_a_5317_, v___x_5340_, v___x_5342_, v___x_5344_);
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v___x_5345_);
v___x_5347_ = v___x_5320_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5345_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v_a_5318_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_dec(v_type_5307_);
v_a_5350_ = lean_ctor_get(v___x_5316_, 0);
v_a_5351_ = lean_ctor_get(v___x_5316_, 1);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5316_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_inc(v_a_5350_);
lean_dec(v___x_5316_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5350_);
lean_ctor_set(v_reuseFailAlloc_5357_, 1, v_a_5351_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5359_, lean_object* v_type_5360_, lean_object* v_ofInterpFn_5361_, lean_object* v_ofLitFn_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5359_, v_type_5360_, v_ofInterpFn_5361_, v_ofLitFn_5362_, v_a_5363_, v_a_5364_);
lean_dec_ref(v_a_5363_);
lean_dec(v_interpStr_5359_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5366_){
_start:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5367_ = lean_unsigned_to_nat(1u);
v___x_5368_ = l_Lean_Syntax_getArg(v_stx_5366_, v___x_5367_);
if (lean_obj_tag(v___x_5368_) == 2)
{
lean_object* v_val_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; 
v_val_5369_ = lean_ctor_get(v___x_5368_, 1);
lean_inc_ref(v_val_5369_);
lean_dec_ref_known(v___x_5368_, 2);
v___x_5370_ = lean_unsigned_to_nat(0u);
v___x_5371_ = lean_string_utf8_byte_size(v_val_5369_);
v___x_5372_ = lean_unsigned_to_nat(2u);
v___x_5373_ = lean_string_pos_sub(v___x_5371_, v___x_5372_);
v___x_5374_ = lean_string_utf8_extract(v_val_5369_, v___x_5370_, v___x_5373_);
lean_dec(v___x_5373_);
lean_dec_ref(v_val_5369_);
return v___x_5374_;
}
else
{
lean_object* v___x_5375_; 
lean_dec(v___x_5368_);
v___x_5375_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_TSyntax_getDocString(v_stx_5376_);
lean_dec(v_stx_5376_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5396_, lean_object* v_prec_5397_){
_start:
{
lean_object* v___y_5399_; lean_object* v___y_5406_; lean_object* v___y_5413_; lean_object* v___y_5420_; lean_object* v___y_5427_; lean_object* v___y_5434_; 
switch(v_x_5396_)
{
case 0:
{
lean_object* v___x_5440_; uint8_t v___x_5441_; 
v___x_5440_ = lean_unsigned_to_nat(1024u);
v___x_5441_ = lean_nat_dec_le(v___x_5440_, v_prec_5397_);
if (v___x_5441_ == 0)
{
lean_object* v___x_5442_; 
v___x_5442_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5399_ = v___x_5442_;
goto v___jp_5398_;
}
else
{
lean_object* v___x_5443_; 
v___x_5443_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5399_ = v___x_5443_;
goto v___jp_5398_;
}
}
case 1:
{
lean_object* v___x_5444_; uint8_t v___x_5445_; 
v___x_5444_ = lean_unsigned_to_nat(1024u);
v___x_5445_ = lean_nat_dec_le(v___x_5444_, v_prec_5397_);
if (v___x_5445_ == 0)
{
lean_object* v___x_5446_; 
v___x_5446_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5406_ = v___x_5446_;
goto v___jp_5405_;
}
else
{
lean_object* v___x_5447_; 
v___x_5447_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5406_ = v___x_5447_;
goto v___jp_5405_;
}
}
case 2:
{
lean_object* v___x_5448_; uint8_t v___x_5449_; 
v___x_5448_ = lean_unsigned_to_nat(1024u);
v___x_5449_ = lean_nat_dec_le(v___x_5448_, v_prec_5397_);
if (v___x_5449_ == 0)
{
lean_object* v___x_5450_; 
v___x_5450_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5413_ = v___x_5450_;
goto v___jp_5412_;
}
else
{
lean_object* v___x_5451_; 
v___x_5451_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5413_ = v___x_5451_;
goto v___jp_5412_;
}
}
case 3:
{
lean_object* v___x_5452_; uint8_t v___x_5453_; 
v___x_5452_ = lean_unsigned_to_nat(1024u);
v___x_5453_ = lean_nat_dec_le(v___x_5452_, v_prec_5397_);
if (v___x_5453_ == 0)
{
lean_object* v___x_5454_; 
v___x_5454_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5420_ = v___x_5454_;
goto v___jp_5419_;
}
else
{
lean_object* v___x_5455_; 
v___x_5455_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5420_ = v___x_5455_;
goto v___jp_5419_;
}
}
case 4:
{
lean_object* v___x_5456_; uint8_t v___x_5457_; 
v___x_5456_ = lean_unsigned_to_nat(1024u);
v___x_5457_ = lean_nat_dec_le(v___x_5456_, v_prec_5397_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5427_ = v___x_5458_;
goto v___jp_5426_;
}
else
{
lean_object* v___x_5459_; 
v___x_5459_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5427_ = v___x_5459_;
goto v___jp_5426_;
}
}
default: 
{
lean_object* v___x_5460_; uint8_t v___x_5461_; 
v___x_5460_ = lean_unsigned_to_nat(1024u);
v___x_5461_ = lean_nat_dec_le(v___x_5460_, v_prec_5397_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5462_; 
v___x_5462_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5434_ = v___x_5462_;
goto v___jp_5433_;
}
else
{
lean_object* v___x_5463_; 
v___x_5463_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5434_ = v___x_5463_;
goto v___jp_5433_;
}
}
}
v___jp_5398_:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; uint8_t v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5400_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5399_);
v___x_5401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___y_5399_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = 0;
v___x_5403_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5403_, 0, v___x_5401_);
lean_ctor_set_uint8(v___x_5403_, sizeof(void*)*1, v___x_5402_);
v___x_5404_ = l_Repr_addAppParen(v___x_5403_, v_prec_5397_);
return v___x_5404_;
}
v___jp_5405_:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5407_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5406_);
v___x_5408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5408_, 0, v___y_5406_);
lean_ctor_set(v___x_5408_, 1, v___x_5407_);
v___x_5409_ = 0;
v___x_5410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5410_, 0, v___x_5408_);
lean_ctor_set_uint8(v___x_5410_, sizeof(void*)*1, v___x_5409_);
v___x_5411_ = l_Repr_addAppParen(v___x_5410_, v_prec_5397_);
return v___x_5411_;
}
v___jp_5412_:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; uint8_t v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5414_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5413_);
v___x_5415_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5415_, 0, v___y_5413_);
lean_ctor_set(v___x_5415_, 1, v___x_5414_);
v___x_5416_ = 0;
v___x_5417_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5417_, 0, v___x_5415_);
lean_ctor_set_uint8(v___x_5417_, sizeof(void*)*1, v___x_5416_);
v___x_5418_ = l_Repr_addAppParen(v___x_5417_, v_prec_5397_);
return v___x_5418_;
}
v___jp_5419_:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; uint8_t v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5421_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5420_);
v___x_5422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5422_, 0, v___y_5420_);
lean_ctor_set(v___x_5422_, 1, v___x_5421_);
v___x_5423_ = 0;
v___x_5424_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5424_, 0, v___x_5422_);
lean_ctor_set_uint8(v___x_5424_, sizeof(void*)*1, v___x_5423_);
v___x_5425_ = l_Repr_addAppParen(v___x_5424_, v_prec_5397_);
return v___x_5425_;
}
v___jp_5426_:
{
lean_object* v___x_5428_; lean_object* v___x_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5428_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5427_);
v___x_5429_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___y_5427_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = 0;
v___x_5431_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5431_, 0, v___x_5429_);
lean_ctor_set_uint8(v___x_5431_, sizeof(void*)*1, v___x_5430_);
v___x_5432_ = l_Repr_addAppParen(v___x_5431_, v_prec_5397_);
return v___x_5432_;
}
v___jp_5433_:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5435_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5434_);
v___x_5436_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5436_, 0, v___y_5434_);
lean_ctor_set(v___x_5436_, 1, v___x_5435_);
v___x_5437_ = 0;
v___x_5438_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5438_, 0, v___x_5436_);
lean_ctor_set_uint8(v___x_5438_, sizeof(void*)*1, v___x_5437_);
v___x_5439_ = l_Repr_addAppParen(v___x_5438_, v_prec_5397_);
return v___x_5439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5464_, lean_object* v_prec_5465_){
_start:
{
uint8_t v_x_341__boxed_5466_; lean_object* v_res_5467_; 
v_x_341__boxed_5466_ = lean_unbox(v_x_5464_);
v_res_5467_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_341__boxed_5466_, v_prec_5465_);
lean_dec(v_prec_5465_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5479_, lean_object* v_prec_5480_){
_start:
{
lean_object* v___y_5482_; lean_object* v___y_5489_; lean_object* v___y_5496_; 
switch(v_x_5479_)
{
case 0:
{
lean_object* v___x_5502_; uint8_t v___x_5503_; 
v___x_5502_ = lean_unsigned_to_nat(1024u);
v___x_5503_ = lean_nat_dec_le(v___x_5502_, v_prec_5480_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5482_ = v___x_5504_;
goto v___jp_5481_;
}
else
{
lean_object* v___x_5505_; 
v___x_5505_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5482_ = v___x_5505_;
goto v___jp_5481_;
}
}
case 1:
{
lean_object* v___x_5506_; uint8_t v___x_5507_; 
v___x_5506_ = lean_unsigned_to_nat(1024u);
v___x_5507_ = lean_nat_dec_le(v___x_5506_, v_prec_5480_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5508_; 
v___x_5508_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5489_ = v___x_5508_;
goto v___jp_5488_;
}
else
{
lean_object* v___x_5509_; 
v___x_5509_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5489_ = v___x_5509_;
goto v___jp_5488_;
}
}
default: 
{
lean_object* v___x_5510_; uint8_t v___x_5511_; 
v___x_5510_ = lean_unsigned_to_nat(1024u);
v___x_5511_ = lean_nat_dec_le(v___x_5510_, v_prec_5480_);
if (v___x_5511_ == 0)
{
lean_object* v___x_5512_; 
v___x_5512_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5496_ = v___x_5512_;
goto v___jp_5495_;
}
else
{
lean_object* v___x_5513_; 
v___x_5513_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5496_ = v___x_5513_;
goto v___jp_5495_;
}
}
}
v___jp_5481_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; uint8_t v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5483_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5482_);
v___x_5484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5484_, 0, v___y_5482_);
lean_ctor_set(v___x_5484_, 1, v___x_5483_);
v___x_5485_ = 0;
v___x_5486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5486_, 0, v___x_5484_);
lean_ctor_set_uint8(v___x_5486_, sizeof(void*)*1, v___x_5485_);
v___x_5487_ = l_Repr_addAppParen(v___x_5486_, v_prec_5480_);
return v___x_5487_;
}
v___jp_5488_:
{
lean_object* v___x_5490_; lean_object* v___x_5491_; uint8_t v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5490_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5489_);
v___x_5491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5491_, 0, v___y_5489_);
lean_ctor_set(v___x_5491_, 1, v___x_5490_);
v___x_5492_ = 0;
v___x_5493_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5493_, 0, v___x_5491_);
lean_ctor_set_uint8(v___x_5493_, sizeof(void*)*1, v___x_5492_);
v___x_5494_ = l_Repr_addAppParen(v___x_5493_, v_prec_5480_);
return v___x_5494_;
}
v___jp_5495_:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; uint8_t v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v___x_5497_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5496_);
v___x_5498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5498_, 0, v___y_5496_);
lean_ctor_set(v___x_5498_, 1, v___x_5497_);
v___x_5499_ = 0;
v___x_5500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5500_, 0, v___x_5498_);
lean_ctor_set_uint8(v___x_5500_, sizeof(void*)*1, v___x_5499_);
v___x_5501_ = l_Repr_addAppParen(v___x_5500_, v_prec_5480_);
return v___x_5501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5514_, lean_object* v_prec_5515_){
_start:
{
uint8_t v_x_173__boxed_5516_; lean_object* v_res_5517_; 
v_x_173__boxed_5516_ = lean_unbox(v_x_5514_);
v_res_5517_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_173__boxed_5516_, v_prec_5515_);
lean_dec(v_prec_5515_);
return v_res_5517_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5529_ = lean_unsigned_to_nat(8u);
v___x_5530_ = lean_nat_to_int(v___x_5529_);
return v___x_5530_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5540_ = lean_unsigned_to_nat(13u);
v___x_5541_ = lean_nat_to_int(v___x_5540_);
return v___x_5541_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; 
v___x_5551_ = lean_unsigned_to_nat(10u);
v___x_5552_ = lean_nat_to_int(v___x_5551_);
return v___x_5552_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; 
v___x_5556_ = lean_unsigned_to_nat(14u);
v___x_5557_ = lean_nat_to_int(v___x_5556_);
return v___x_5557_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; 
v___x_5561_ = lean_unsigned_to_nat(19u);
v___x_5562_ = lean_nat_to_int(v___x_5561_);
return v___x_5562_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5566_; lean_object* v___x_5567_; 
v___x_5566_ = lean_unsigned_to_nat(20u);
v___x_5567_ = lean_nat_to_int(v___x_5566_);
return v___x_5567_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; 
v___x_5574_ = lean_unsigned_to_nat(9u);
v___x_5575_ = lean_nat_to_int(v___x_5574_);
return v___x_5575_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5582_; lean_object* v___x_5583_; 
v___x_5582_ = lean_unsigned_to_nat(12u);
v___x_5583_ = lean_nat_to_int(v___x_5582_);
return v___x_5583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5590_){
_start:
{
uint8_t v_zeta_5591_; uint8_t v_beta_5592_; uint8_t v_eta_5593_; uint8_t v_etaStruct_5594_; uint8_t v_iota_5595_; uint8_t v_proj_5596_; uint8_t v_decide_5597_; uint8_t v_autoUnfold_5598_; uint8_t v_failIfUnchanged_5599_; uint8_t v_unfoldPartialApp_5600_; uint8_t v_zetaDelta_5601_; uint8_t v_index_5602_; uint8_t v_zetaUnused_5603_; uint8_t v_zetaHave_5604_; uint8_t v_locals_5605_; uint8_t v_instances_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; uint8_t v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; 
v_zeta_5591_ = lean_ctor_get_uint8(v_x_5590_, 0);
v_beta_5592_ = lean_ctor_get_uint8(v_x_5590_, 1);
v_eta_5593_ = lean_ctor_get_uint8(v_x_5590_, 2);
v_etaStruct_5594_ = lean_ctor_get_uint8(v_x_5590_, 3);
v_iota_5595_ = lean_ctor_get_uint8(v_x_5590_, 4);
v_proj_5596_ = lean_ctor_get_uint8(v_x_5590_, 5);
v_decide_5597_ = lean_ctor_get_uint8(v_x_5590_, 6);
v_autoUnfold_5598_ = lean_ctor_get_uint8(v_x_5590_, 7);
v_failIfUnchanged_5599_ = lean_ctor_get_uint8(v_x_5590_, 8);
v_unfoldPartialApp_5600_ = lean_ctor_get_uint8(v_x_5590_, 9);
v_zetaDelta_5601_ = lean_ctor_get_uint8(v_x_5590_, 10);
v_index_5602_ = lean_ctor_get_uint8(v_x_5590_, 11);
v_zetaUnused_5603_ = lean_ctor_get_uint8(v_x_5590_, 12);
v_zetaHave_5604_ = lean_ctor_get_uint8(v_x_5590_, 13);
v_locals_5605_ = lean_ctor_get_uint8(v_x_5590_, 14);
v_instances_5606_ = lean_ctor_get_uint8(v_x_5590_, 15);
v___x_5607_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5608_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5609_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5610_ = lean_unsigned_to_nat(0u);
v___x_5611_ = l_Bool_repr___redArg(v_zeta_5591_);
v___x_5612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5609_);
lean_ctor_set(v___x_5612_, 1, v___x_5611_);
v___x_5613_ = 0;
v___x_5614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5614_, 0, v___x_5612_);
lean_ctor_set_uint8(v___x_5614_, sizeof(void*)*1, v___x_5613_);
v___x_5615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5608_);
lean_ctor_set(v___x_5615_, 1, v___x_5614_);
v___x_5616_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5615_);
lean_ctor_set(v___x_5617_, 1, v___x_5616_);
v___x_5618_ = lean_box(1);
v___x_5619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5617_);
lean_ctor_set(v___x_5619_, 1, v___x_5618_);
v___x_5620_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5619_);
lean_ctor_set(v___x_5621_, 1, v___x_5620_);
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
lean_ctor_set(v___x_5622_, 1, v___x_5607_);
v___x_5623_ = l_Bool_repr___redArg(v_beta_5592_);
v___x_5624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5609_);
lean_ctor_set(v___x_5624_, 1, v___x_5623_);
v___x_5625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5625_, 0, v___x_5624_);
lean_ctor_set_uint8(v___x_5625_, sizeof(void*)*1, v___x_5613_);
v___x_5626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5622_);
lean_ctor_set(v___x_5626_, 1, v___x_5625_);
v___x_5627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set(v___x_5627_, 1, v___x_5616_);
v___x_5628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5627_);
lean_ctor_set(v___x_5628_, 1, v___x_5618_);
v___x_5629_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5628_);
lean_ctor_set(v___x_5630_, 1, v___x_5629_);
v___x_5631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5630_);
lean_ctor_set(v___x_5631_, 1, v___x_5607_);
v___x_5632_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5633_ = l_Bool_repr___redArg(v_eta_5593_);
v___x_5634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5632_);
lean_ctor_set(v___x_5634_, 1, v___x_5633_);
v___x_5635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5635_, 0, v___x_5634_);
lean_ctor_set_uint8(v___x_5635_, sizeof(void*)*1, v___x_5613_);
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5631_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set(v___x_5637_, 1, v___x_5616_);
v___x_5638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5637_);
lean_ctor_set(v___x_5638_, 1, v___x_5618_);
v___x_5639_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5638_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
lean_ctor_set(v___x_5641_, 1, v___x_5607_);
v___x_5642_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5643_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5594_, v___x_5610_);
v___x_5644_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5642_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
v___x_5645_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set_uint8(v___x_5645_, sizeof(void*)*1, v___x_5613_);
v___x_5646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5641_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set(v___x_5647_, 1, v___x_5616_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
lean_ctor_set(v___x_5648_, 1, v___x_5618_);
v___x_5649_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5648_);
lean_ctor_set(v___x_5650_, 1, v___x_5649_);
v___x_5651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set(v___x_5651_, 1, v___x_5607_);
v___x_5652_ = l_Bool_repr___redArg(v_iota_5595_);
v___x_5653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5609_);
lean_ctor_set(v___x_5653_, 1, v___x_5652_);
v___x_5654_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set_uint8(v___x_5654_, sizeof(void*)*1, v___x_5613_);
v___x_5655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5651_);
lean_ctor_set(v___x_5655_, 1, v___x_5654_);
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5655_);
lean_ctor_set(v___x_5656_, 1, v___x_5616_);
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set(v___x_5657_, 1, v___x_5618_);
v___x_5658_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5657_);
lean_ctor_set(v___x_5659_, 1, v___x_5658_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set(v___x_5660_, 1, v___x_5607_);
v___x_5661_ = l_Bool_repr___redArg(v_proj_5596_);
v___x_5662_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5609_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set_uint8(v___x_5663_, sizeof(void*)*1, v___x_5613_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5660_);
lean_ctor_set(v___x_5664_, 1, v___x_5663_);
v___x_5665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
lean_ctor_set(v___x_5665_, 1, v___x_5616_);
v___x_5666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
lean_ctor_set(v___x_5666_, 1, v___x_5618_);
v___x_5667_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5666_);
lean_ctor_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set(v___x_5669_, 1, v___x_5607_);
v___x_5670_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5671_ = l_Bool_repr___redArg(v_decide_5597_);
v___x_5672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5670_);
lean_ctor_set(v___x_5672_, 1, v___x_5671_);
v___x_5673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
lean_ctor_set_uint8(v___x_5673_, sizeof(void*)*1, v___x_5613_);
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5669_);
lean_ctor_set(v___x_5674_, 1, v___x_5673_);
v___x_5675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set(v___x_5675_, 1, v___x_5616_);
v___x_5676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
lean_ctor_set(v___x_5676_, 1, v___x_5618_);
v___x_5677_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5676_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set(v___x_5679_, 1, v___x_5607_);
v___x_5680_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5681_ = l_Bool_repr___redArg(v_autoUnfold_5598_);
v___x_5682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5680_);
lean_ctor_set(v___x_5682_, 1, v___x_5681_);
v___x_5683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
lean_ctor_set_uint8(v___x_5683_, sizeof(void*)*1, v___x_5613_);
v___x_5684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5679_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set(v___x_5685_, 1, v___x_5616_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
lean_ctor_set(v___x_5686_, 1, v___x_5618_);
v___x_5687_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5686_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5688_);
lean_ctor_set(v___x_5689_, 1, v___x_5607_);
v___x_5690_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5691_ = l_Bool_repr___redArg(v_failIfUnchanged_5599_);
v___x_5692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5690_);
lean_ctor_set(v___x_5692_, 1, v___x_5691_);
v___x_5693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5693_, 0, v___x_5692_);
lean_ctor_set_uint8(v___x_5693_, sizeof(void*)*1, v___x_5613_);
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5689_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5616_);
v___x_5696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5695_);
lean_ctor_set(v___x_5696_, 1, v___x_5618_);
v___x_5697_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set(v___x_5699_, 1, v___x_5607_);
v___x_5700_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5701_ = l_Bool_repr___redArg(v_unfoldPartialApp_5600_);
v___x_5702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*1, v___x_5613_);
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5699_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v___x_5616_);
v___x_5706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
lean_ctor_set(v___x_5706_, 1, v___x_5618_);
v___x_5707_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5706_);
lean_ctor_set(v___x_5708_, 1, v___x_5707_);
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set(v___x_5709_, 1, v___x_5607_);
v___x_5710_ = l_Bool_repr___redArg(v_zetaDelta_5601_);
v___x_5711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5642_);
lean_ctor_set(v___x_5711_, 1, v___x_5710_);
v___x_5712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
lean_ctor_set_uint8(v___x_5712_, sizeof(void*)*1, v___x_5613_);
v___x_5713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5709_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5713_);
lean_ctor_set(v___x_5714_, 1, v___x_5616_);
v___x_5715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set(v___x_5715_, 1, v___x_5618_);
v___x_5716_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5715_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set(v___x_5718_, 1, v___x_5607_);
v___x_5719_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5720_ = l_Bool_repr___redArg(v_index_5602_);
v___x_5721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5719_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5722_, 0, v___x_5721_);
lean_ctor_set_uint8(v___x_5722_, sizeof(void*)*1, v___x_5613_);
v___x_5723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5718_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5723_);
lean_ctor_set(v___x_5724_, 1, v___x_5616_);
v___x_5725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
lean_ctor_set(v___x_5725_, 1, v___x_5618_);
v___x_5726_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5725_);
lean_ctor_set(v___x_5727_, 1, v___x_5726_);
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
lean_ctor_set(v___x_5728_, 1, v___x_5607_);
v___x_5729_ = l_Bool_repr___redArg(v_zetaUnused_5603_);
v___x_5730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5680_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
lean_ctor_set_uint8(v___x_5731_, sizeof(void*)*1, v___x_5613_);
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5728_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5732_);
lean_ctor_set(v___x_5733_, 1, v___x_5616_);
v___x_5734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5733_);
lean_ctor_set(v___x_5734_, 1, v___x_5618_);
v___x_5735_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5734_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v___x_5607_);
v___x_5738_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5739_ = l_Bool_repr___redArg(v_zetaHave_5604_);
v___x_5740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5738_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5741_, 0, v___x_5740_);
lean_ctor_set_uint8(v___x_5741_, sizeof(void*)*1, v___x_5613_);
v___x_5742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5737_);
lean_ctor_set(v___x_5742_, 1, v___x_5741_);
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5742_);
lean_ctor_set(v___x_5743_, 1, v___x_5616_);
v___x_5744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set(v___x_5744_, 1, v___x_5618_);
v___x_5745_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5744_);
lean_ctor_set(v___x_5746_, 1, v___x_5745_);
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5746_);
lean_ctor_set(v___x_5747_, 1, v___x_5607_);
v___x_5748_ = l_Bool_repr___redArg(v_locals_5605_);
v___x_5749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5670_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set_uint8(v___x_5750_, sizeof(void*)*1, v___x_5613_);
v___x_5751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5747_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
lean_ctor_set(v___x_5752_, 1, v___x_5616_);
v___x_5753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
lean_ctor_set(v___x_5753_, 1, v___x_5618_);
v___x_5754_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5753_);
lean_ctor_set(v___x_5755_, 1, v___x_5754_);
v___x_5756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
lean_ctor_set(v___x_5756_, 1, v___x_5607_);
v___x_5757_ = l_Bool_repr___redArg(v_instances_5606_);
v___x_5758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5642_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v___x_5759_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5759_, 0, v___x_5758_);
lean_ctor_set_uint8(v___x_5759_, sizeof(void*)*1, v___x_5613_);
v___x_5760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5756_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5762_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___x_5762_);
lean_ctor_set(v___x_5763_, 1, v___x_5760_);
v___x_5764_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5763_);
lean_ctor_set(v___x_5765_, 1, v___x_5764_);
v___x_5766_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5761_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set_uint8(v___x_5767_, sizeof(void*)*1, v___x_5613_);
return v___x_5767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5768_);
lean_dec_ref(v_x_5768_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5770_, lean_object* v_prec_5771_){
_start:
{
lean_object* v___x_5772_; 
v___x_5772_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5770_);
return v___x_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5773_, lean_object* v_prec_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l_Lean_Meta_instReprConfig_repr(v_x_5773_, v_prec_5774_);
lean_dec(v_prec_5774_);
lean_dec_ref(v_x_5773_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5783_, lean_object* v_x_5784_){
_start:
{
if (lean_obj_tag(v_x_5783_) == 0)
{
lean_object* v___x_5785_; 
v___x_5785_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5785_;
}
else
{
lean_object* v_val_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5797_; 
v_val_5786_ = lean_ctor_get(v_x_5783_, 0);
v_isSharedCheck_5797_ = !lean_is_exclusive(v_x_5783_);
if (v_isSharedCheck_5797_ == 0)
{
v___x_5788_ = v_x_5783_;
v_isShared_5789_ = v_isSharedCheck_5797_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_val_5786_);
lean_dec(v_x_5783_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5797_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5793_; 
v___x_5790_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5791_ = l_Nat_reprFast(v_val_5786_);
if (v_isShared_5789_ == 0)
{
lean_ctor_set_tag(v___x_5788_, 3);
lean_ctor_set(v___x_5788_, 0, v___x_5791_);
v___x_5793_ = v___x_5788_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5790_);
lean_ctor_set(v___x_5794_, 1, v___x_5793_);
v___x_5795_ = l_Repr_addAppParen(v___x_5794_, v_x_5784_);
return v___x_5795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5798_, lean_object* v_x_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5798_, v_x_5799_);
lean_dec(v_x_5799_);
return v_res_5800_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = lean_unsigned_to_nat(21u);
v___x_5814_ = lean_nat_to_int(v___x_5813_);
return v___x_5814_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = lean_unsigned_to_nat(11u);
v___x_5822_ = lean_nat_to_int(v___x_5821_);
return v___x_5822_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_unsigned_to_nat(23u);
v___x_5839_ = lean_nat_to_int(v___x_5838_);
return v___x_5839_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5843_ = lean_unsigned_to_nat(16u);
v___x_5844_ = lean_nat_to_int(v___x_5843_);
return v___x_5844_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = lean_unsigned_to_nat(15u);
v___x_5852_ = lean_nat_to_int(v___x_5851_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = lean_unsigned_to_nat(17u);
v___x_5860_ = lean_nat_to_int(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5867_ = lean_unsigned_to_nat(18u);
v___x_5868_ = lean_nat_to_int(v___x_5867_);
return v___x_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5869_){
_start:
{
lean_object* v_maxSteps_5870_; lean_object* v_maxDischargeDepth_5871_; uint8_t v_contextual_5872_; uint8_t v_memoize_5873_; uint8_t v_singlePass_5874_; uint8_t v_zeta_5875_; uint8_t v_beta_5876_; uint8_t v_eta_5877_; uint8_t v_etaStruct_5878_; uint8_t v_iota_5879_; uint8_t v_proj_5880_; uint8_t v_decide_5881_; uint8_t v_arith_5882_; uint8_t v_autoUnfold_5883_; uint8_t v_dsimp_5884_; uint8_t v_failIfUnchanged_5885_; uint8_t v_ground_5886_; uint8_t v_unfoldPartialApp_5887_; uint8_t v_zetaDelta_5888_; uint8_t v_index_5889_; uint8_t v_implicitDefEqProofs_5890_; uint8_t v_zetaUnused_5891_; uint8_t v_catchRuntime_5892_; uint8_t v_zetaHave_5893_; uint8_t v_letToHave_5894_; uint8_t v_congrConsts_5895_; uint8_t v_bitVecOfNat_5896_; uint8_t v_warnExponents_5897_; uint8_t v_suggestions_5898_; lean_object* v_maxSuggestions_5899_; uint8_t v_locals_5900_; uint8_t v_instances_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; uint8_t v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
v_maxSteps_5870_ = lean_ctor_get(v_x_5869_, 0);
lean_inc(v_maxSteps_5870_);
v_maxDischargeDepth_5871_ = lean_ctor_get(v_x_5869_, 1);
lean_inc(v_maxDischargeDepth_5871_);
v_contextual_5872_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3);
v_memoize_5873_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 1);
v_singlePass_5874_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 2);
v_zeta_5875_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 3);
v_beta_5876_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 4);
v_eta_5877_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 5);
v_etaStruct_5878_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 6);
v_iota_5879_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 7);
v_proj_5880_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 8);
v_decide_5881_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 9);
v_arith_5882_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 10);
v_autoUnfold_5883_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 11);
v_dsimp_5884_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5885_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 13);
v_ground_5886_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5887_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 15);
v_zetaDelta_5888_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 16);
v_index_5889_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5890_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 18);
v_zetaUnused_5891_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 19);
v_catchRuntime_5892_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 20);
v_zetaHave_5893_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 21);
v_letToHave_5894_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 22);
v_congrConsts_5895_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5896_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 24);
v_warnExponents_5897_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 25);
v_suggestions_5898_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 26);
v_maxSuggestions_5899_ = lean_ctor_get(v_x_5869_, 2);
lean_inc(v_maxSuggestions_5899_);
v_locals_5900_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 27);
v_instances_5901_ = lean_ctor_get_uint8(v_x_5869_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5869_);
v___x_5902_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5903_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5904_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5905_ = l_Nat_reprFast(v_maxSteps_5870_);
v___x_5906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5905_);
v___x_5907_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5904_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = 0;
v___x_5909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5909_, 0, v___x_5907_);
lean_ctor_set_uint8(v___x_5909_, sizeof(void*)*1, v___x_5908_);
v___x_5910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5903_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = lean_box(1);
v___x_5914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5912_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v___x_5915_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5914_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5916_);
lean_ctor_set(v___x_5917_, 1, v___x_5902_);
v___x_5918_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5919_ = l_Nat_reprFast(v_maxDischargeDepth_5871_);
v___x_5920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5919_);
v___x_5921_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5918_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
lean_ctor_set_uint8(v___x_5922_, sizeof(void*)*1, v___x_5908_);
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5917_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5923_);
lean_ctor_set(v___x_5924_, 1, v___x_5911_);
v___x_5925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5925_, 0, v___x_5924_);
lean_ctor_set(v___x_5925_, 1, v___x_5913_);
v___x_5926_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5925_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
v___x_5928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set(v___x_5928_, 1, v___x_5902_);
v___x_5929_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5930_ = lean_unsigned_to_nat(0u);
v___x_5931_ = l_Bool_repr___redArg(v_contextual_5872_);
v___x_5932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5929_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5933_, 0, v___x_5932_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*1, v___x_5908_);
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5928_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v___x_5911_);
v___x_5936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5935_);
lean_ctor_set(v___x_5936_, 1, v___x_5913_);
v___x_5937_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set(v___x_5939_, 1, v___x_5902_);
v___x_5940_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5941_ = l_Bool_repr___redArg(v_memoize_5873_);
v___x_5942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5943_, 0, v___x_5942_);
lean_ctor_set_uint8(v___x_5943_, sizeof(void*)*1, v___x_5908_);
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5939_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set(v___x_5945_, 1, v___x_5911_);
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
lean_ctor_set(v___x_5946_, 1, v___x_5913_);
v___x_5947_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5946_);
lean_ctor_set(v___x_5948_, 1, v___x_5947_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set(v___x_5949_, 1, v___x_5902_);
v___x_5950_ = l_Bool_repr___redArg(v_singlePass_5874_);
v___x_5951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5929_);
lean_ctor_set(v___x_5951_, 1, v___x_5950_);
v___x_5952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
lean_ctor_set_uint8(v___x_5952_, sizeof(void*)*1, v___x_5908_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5949_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set(v___x_5954_, 1, v___x_5911_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set(v___x_5955_, 1, v___x_5913_);
v___x_5956_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5955_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5902_);
v___x_5959_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5960_ = l_Bool_repr___redArg(v_zeta_5875_);
v___x_5961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5959_);
lean_ctor_set(v___x_5961_, 1, v___x_5960_);
v___x_5962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_ctor_set_uint8(v___x_5962_, sizeof(void*)*1, v___x_5908_);
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5958_);
lean_ctor_set(v___x_5963_, 1, v___x_5962_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5963_);
lean_ctor_set(v___x_5964_, 1, v___x_5911_);
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set(v___x_5965_, 1, v___x_5913_);
v___x_5966_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5965_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5967_);
lean_ctor_set(v___x_5968_, 1, v___x_5902_);
v___x_5969_ = l_Bool_repr___redArg(v_beta_5876_);
v___x_5970_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5959_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
v___x_5971_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
lean_ctor_set_uint8(v___x_5971_, sizeof(void*)*1, v___x_5908_);
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5968_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
v___x_5973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set(v___x_5973_, 1, v___x_5911_);
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5973_);
lean_ctor_set(v___x_5974_, 1, v___x_5913_);
v___x_5975_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5974_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
lean_ctor_set(v___x_5977_, 1, v___x_5902_);
v___x_5978_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5979_ = l_Bool_repr___redArg(v_eta_5877_);
v___x_5980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5978_);
lean_ctor_set(v___x_5980_, 1, v___x_5979_);
v___x_5981_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5981_, 0, v___x_5980_);
lean_ctor_set_uint8(v___x_5981_, sizeof(void*)*1, v___x_5908_);
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5977_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
lean_ctor_set(v___x_5983_, 1, v___x_5911_);
v___x_5984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set(v___x_5984_, 1, v___x_5913_);
v___x_5985_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5984_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5902_);
v___x_5988_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5989_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5878_, v___x_5930_);
v___x_5990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5988_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
lean_ctor_set_uint8(v___x_5991_, sizeof(void*)*1, v___x_5908_);
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5987_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set(v___x_5993_, 1, v___x_5911_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set(v___x_5994_, 1, v___x_5913_);
v___x_5995_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5994_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set(v___x_5997_, 1, v___x_5902_);
v___x_5998_ = l_Bool_repr___redArg(v_iota_5879_);
v___x_5999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5959_);
lean_ctor_set(v___x_5999_, 1, v___x_5998_);
v___x_6000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set_uint8(v___x_6000_, sizeof(void*)*1, v___x_5908_);
v___x_6001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_5997_);
lean_ctor_set(v___x_6001_, 1, v___x_6000_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6001_);
lean_ctor_set(v___x_6002_, 1, v___x_5911_);
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v___x_5913_);
v___x_6004_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6003_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___x_5902_);
v___x_6007_ = l_Bool_repr___redArg(v_proj_5880_);
v___x_6008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_5959_);
lean_ctor_set(v___x_6008_, 1, v___x_6007_);
v___x_6009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6009_, 0, v___x_6008_);
lean_ctor_set_uint8(v___x_6009_, sizeof(void*)*1, v___x_5908_);
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6006_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set(v___x_6011_, 1, v___x_5911_);
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6011_);
lean_ctor_set(v___x_6012_, 1, v___x_5913_);
v___x_6013_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6012_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set(v___x_6015_, 1, v___x_5902_);
v___x_6016_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6017_ = l_Bool_repr___redArg(v_decide_5881_);
v___x_6018_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6016_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
lean_ctor_set_uint8(v___x_6019_, sizeof(void*)*1, v___x_5908_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6015_);
lean_ctor_set(v___x_6020_, 1, v___x_6019_);
v___x_6021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set(v___x_6021_, 1, v___x_5911_);
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
lean_ctor_set(v___x_6022_, 1, v___x_5913_);
v___x_6023_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6022_);
lean_ctor_set(v___x_6024_, 1, v___x_6023_);
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set(v___x_6025_, 1, v___x_5902_);
v___x_6026_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6027_ = l_Bool_repr___redArg(v_arith_5882_);
v___x_6028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6026_);
lean_ctor_set(v___x_6028_, 1, v___x_6027_);
v___x_6029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set_uint8(v___x_6029_, sizeof(void*)*1, v___x_5908_);
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6025_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set(v___x_6031_, 1, v___x_5911_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_5913_);
v___x_6033_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6032_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set(v___x_6035_, 1, v___x_5902_);
v___x_6036_ = l_Bool_repr___redArg(v_autoUnfold_5883_);
v___x_6037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_5929_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set_uint8(v___x_6038_, sizeof(void*)*1, v___x_5908_);
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6035_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set(v___x_6040_, 1, v___x_5911_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_5913_);
v___x_6042_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6041_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_5902_);
v___x_6045_ = l_Bool_repr___redArg(v_dsimp_5884_);
v___x_6046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6026_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6047_, 0, v___x_6046_);
lean_ctor_set_uint8(v___x_6047_, sizeof(void*)*1, v___x_5908_);
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6044_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6048_);
lean_ctor_set(v___x_6049_, 1, v___x_5911_);
v___x_6050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
lean_ctor_set(v___x_6050_, 1, v___x_5913_);
v___x_6051_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6050_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set(v___x_6053_, 1, v___x_5902_);
v___x_6054_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6055_ = l_Bool_repr___redArg(v_failIfUnchanged_5885_);
v___x_6056_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6054_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set_uint8(v___x_6057_, sizeof(void*)*1, v___x_5908_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6053_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set(v___x_6059_, 1, v___x_5911_);
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
lean_ctor_set(v___x_6060_, 1, v___x_5913_);
v___x_6061_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6060_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5902_);
v___x_6064_ = l_Bool_repr___redArg(v_ground_5886_);
v___x_6065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6016_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
lean_ctor_set_uint8(v___x_6066_, sizeof(void*)*1, v___x_5908_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6063_);
lean_ctor_set(v___x_6067_, 1, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
lean_ctor_set(v___x_6068_, 1, v___x_5911_);
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set(v___x_6069_, 1, v___x_5913_);
v___x_6070_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6069_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_5902_);
v___x_6073_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6074_ = l_Bool_repr___redArg(v_unfoldPartialApp_5887_);
v___x_6075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6073_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
v___x_6076_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set_uint8(v___x_6076_, sizeof(void*)*1, v___x_5908_);
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6072_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
lean_ctor_set(v___x_6078_, 1, v___x_5911_);
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set(v___x_6079_, 1, v___x_5913_);
v___x_6080_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6079_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5902_);
v___x_6083_ = l_Bool_repr___redArg(v_zetaDelta_5888_);
v___x_6084_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_5988_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set_uint8(v___x_6085_, sizeof(void*)*1, v___x_5908_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6082_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
lean_ctor_set(v___x_6087_, 1, v___x_5911_);
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set(v___x_6088_, 1, v___x_5913_);
v___x_6089_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6088_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_5902_);
v___x_6092_ = l_Bool_repr___redArg(v_index_5889_);
v___x_6093_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6026_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set_uint8(v___x_6094_, sizeof(void*)*1, v___x_5908_);
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6091_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_5911_);
v___x_6097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6096_);
lean_ctor_set(v___x_6097_, 1, v___x_5913_);
v___x_6098_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6097_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_5902_);
v___x_6101_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6102_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5890_);
v___x_6103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set_uint8(v___x_6104_, sizeof(void*)*1, v___x_5908_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6100_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
v___x_6106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set(v___x_6106_, 1, v___x_5911_);
v___x_6107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set(v___x_6107_, 1, v___x_5913_);
v___x_6108_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6107_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_5902_);
v___x_6111_ = l_Bool_repr___redArg(v_zetaUnused_5891_);
v___x_6112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_5929_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set_uint8(v___x_6113_, sizeof(void*)*1, v___x_5908_);
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6110_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_5911_);
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v___x_5913_);
v___x_6117_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6116_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_5902_);
v___x_6120_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6121_ = l_Bool_repr___redArg(v_catchRuntime_5892_);
v___x_6122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6120_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set_uint8(v___x_6123_, sizeof(void*)*1, v___x_5908_);
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6119_);
lean_ctor_set(v___x_6124_, 1, v___x_6123_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6124_);
lean_ctor_set(v___x_6125_, 1, v___x_5911_);
v___x_6126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set(v___x_6126_, 1, v___x_5913_);
v___x_6127_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6126_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_5902_);
v___x_6130_ = l_Bool_repr___redArg(v_zetaHave_5893_);
v___x_6131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_5904_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set_uint8(v___x_6132_, sizeof(void*)*1, v___x_5908_);
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6129_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
v___x_6134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
lean_ctor_set(v___x_6134_, 1, v___x_5911_);
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set(v___x_6135_, 1, v___x_5913_);
v___x_6136_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6135_);
lean_ctor_set(v___x_6137_, 1, v___x_6136_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_5902_);
v___x_6139_ = l_Bool_repr___redArg(v_letToHave_5894_);
v___x_6140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_5988_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6141_, 0, v___x_6140_);
lean_ctor_set_uint8(v___x_6141_, sizeof(void*)*1, v___x_5908_);
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6138_);
lean_ctor_set(v___x_6142_, 1, v___x_6141_);
v___x_6143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set(v___x_6143_, 1, v___x_5911_);
v___x_6144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6143_);
lean_ctor_set(v___x_6144_, 1, v___x_5913_);
v___x_6145_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6144_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set(v___x_6147_, 1, v___x_5902_);
v___x_6148_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6149_ = l_Bool_repr___redArg(v_congrConsts_5895_);
v___x_6150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set_uint8(v___x_6151_, sizeof(void*)*1, v___x_5908_);
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6147_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
v___x_6153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6152_);
lean_ctor_set(v___x_6153_, 1, v___x_5911_);
v___x_6154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6153_);
lean_ctor_set(v___x_6154_, 1, v___x_5913_);
v___x_6155_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6154_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set(v___x_6157_, 1, v___x_5902_);
v___x_6158_ = l_Bool_repr___redArg(v_bitVecOfNat_5896_);
v___x_6159_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6148_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set_uint8(v___x_6160_, sizeof(void*)*1, v___x_5908_);
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6157_);
lean_ctor_set(v___x_6161_, 1, v___x_6160_);
v___x_6162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6161_);
lean_ctor_set(v___x_6162_, 1, v___x_5911_);
v___x_6163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6162_);
lean_ctor_set(v___x_6163_, 1, v___x_5913_);
v___x_6164_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6163_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set(v___x_6166_, 1, v___x_5902_);
v___x_6167_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6168_ = l_Bool_repr___redArg(v_warnExponents_5897_);
v___x_6169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6167_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
lean_ctor_set_uint8(v___x_6170_, sizeof(void*)*1, v___x_5908_);
v___x_6171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6166_);
lean_ctor_set(v___x_6171_, 1, v___x_6170_);
v___x_6172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6171_);
lean_ctor_set(v___x_6172_, 1, v___x_5911_);
v___x_6173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set(v___x_6173_, 1, v___x_5913_);
v___x_6174_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6173_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set(v___x_6176_, 1, v___x_5902_);
v___x_6177_ = l_Bool_repr___redArg(v_suggestions_5898_);
v___x_6178_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6148_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set_uint8(v___x_6179_, sizeof(void*)*1, v___x_5908_);
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6176_);
lean_ctor_set(v___x_6180_, 1, v___x_6179_);
v___x_6181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
lean_ctor_set(v___x_6181_, 1, v___x_5911_);
v___x_6182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6181_);
lean_ctor_set(v___x_6182_, 1, v___x_5913_);
v___x_6183_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6182_);
lean_ctor_set(v___x_6184_, 1, v___x_6183_);
v___x_6185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___x_5902_);
v___x_6186_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6187_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5899_, v___x_5930_);
v___x_6188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
lean_ctor_set_uint8(v___x_6189_, sizeof(void*)*1, v___x_5908_);
v___x_6190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6185_);
lean_ctor_set(v___x_6190_, 1, v___x_6189_);
v___x_6191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6190_);
lean_ctor_set(v___x_6191_, 1, v___x_5911_);
v___x_6192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set(v___x_6192_, 1, v___x_5913_);
v___x_6193_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6192_);
lean_ctor_set(v___x_6194_, 1, v___x_6193_);
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6194_);
lean_ctor_set(v___x_6195_, 1, v___x_5902_);
v___x_6196_ = l_Bool_repr___redArg(v_locals_5900_);
v___x_6197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6016_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set_uint8(v___x_6198_, sizeof(void*)*1, v___x_5908_);
v___x_6199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6195_);
lean_ctor_set(v___x_6199_, 1, v___x_6198_);
v___x_6200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6199_);
lean_ctor_set(v___x_6200_, 1, v___x_5911_);
v___x_6201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6200_);
lean_ctor_set(v___x_6201_, 1, v___x_5913_);
v___x_6202_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6201_);
lean_ctor_set(v___x_6203_, 1, v___x_6202_);
v___x_6204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6203_);
lean_ctor_set(v___x_6204_, 1, v___x_5902_);
v___x_6205_ = l_Bool_repr___redArg(v_instances_5901_);
v___x_6206_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_5988_);
lean_ctor_set(v___x_6206_, 1, v___x_6205_);
v___x_6207_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
lean_ctor_set_uint8(v___x_6207_, sizeof(void*)*1, v___x_5908_);
v___x_6208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6204_);
lean_ctor_set(v___x_6208_, 1, v___x_6207_);
v___x_6209_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6210_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
lean_ctor_set(v___x_6211_, 1, v___x_6208_);
v___x_6212_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6211_);
lean_ctor_set(v___x_6213_, 1, v___x_6212_);
v___x_6214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6209_);
lean_ctor_set(v___x_6214_, 1, v___x_6213_);
v___x_6215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6215_, 0, v___x_6214_);
lean_ctor_set_uint8(v___x_6215_, sizeof(void*)*1, v___x_5908_);
return v___x_6215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6216_, lean_object* v_prec_6217_){
_start:
{
lean_object* v___x_6218_; 
v___x_6218_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6216_);
return v___x_6218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6219_, lean_object* v_prec_6220_){
_start:
{
lean_object* v_res_6221_; 
v_res_6221_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6219_, v_prec_6220_);
lean_dec(v_prec_6220_);
return v_res_6221_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6224_, lean_object* v_x_6225_){
_start:
{
if (lean_obj_tag(v_x_6225_) == 0)
{
uint8_t v___x_6226_; 
v___x_6226_ = 0;
return v___x_6226_;
}
else
{
lean_object* v_head_6227_; lean_object* v_tail_6228_; uint8_t v___x_6229_; 
v_head_6227_ = lean_ctor_get(v_x_6225_, 0);
v_tail_6228_ = lean_ctor_get(v_x_6225_, 1);
v___x_6229_ = lean_nat_dec_eq(v_a_6224_, v_head_6227_);
if (v___x_6229_ == 0)
{
v_x_6225_ = v_tail_6228_;
goto _start;
}
else
{
return v___x_6229_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6231_, lean_object* v_x_6232_){
_start:
{
uint8_t v_res_6233_; lean_object* v_r_6234_; 
v_res_6233_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6231_, v_x_6232_);
lean_dec(v_x_6232_);
lean_dec(v_a_6231_);
v_r_6234_ = lean_box(v_res_6233_);
return v_r_6234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6235_, lean_object* v_x_6236_){
_start:
{
switch(lean_obj_tag(v_x_6235_))
{
case 0:
{
uint8_t v___x_6237_; 
v___x_6237_ = 1;
return v___x_6237_;
}
case 1:
{
lean_object* v_idxs_6238_; uint8_t v___x_6239_; 
v_idxs_6238_ = lean_ctor_get(v_x_6235_, 0);
v___x_6239_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6236_, v_idxs_6238_);
return v___x_6239_;
}
default: 
{
lean_object* v_idxs_6240_; uint8_t v___x_6241_; 
v_idxs_6240_ = lean_ctor_get(v_x_6235_, 0);
v___x_6241_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6236_, v_idxs_6240_);
if (v___x_6241_ == 0)
{
uint8_t v___x_6242_; 
v___x_6242_ = 1;
return v___x_6242_;
}
else
{
uint8_t v___x_6243_; 
v___x_6243_ = 0;
return v___x_6243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6244_, lean_object* v_x_6245_){
_start:
{
uint8_t v_res_6246_; lean_object* v_r_6247_; 
v_res_6246_ = l_Lean_Meta_Occurrences_contains(v_x_6244_, v_x_6245_);
lean_dec(v_x_6245_);
lean_dec(v_x_6244_);
v_r_6247_ = lean_box(v_res_6246_);
return v_r_6247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6248_){
_start:
{
if (lean_obj_tag(v_x_6248_) == 0)
{
uint8_t v___x_6249_; 
v___x_6249_ = 1;
return v___x_6249_;
}
else
{
uint8_t v___x_6250_; 
v___x_6250_ = 0;
return v___x_6250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6251_){
_start:
{
uint8_t v_res_6252_; lean_object* v_r_6253_; 
v_res_6252_ = l_Lean_Meta_Occurrences_isAll(v_x_6251_);
lean_dec(v_x_6251_);
v_r_6253_ = lean_box(v_res_6252_);
return v_r_6253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6254_){
_start:
{
switch(v_x_6254_)
{
case 0:
{
lean_object* v___x_6255_; 
v___x_6255_ = lean_unsigned_to_nat(0u);
return v___x_6255_;
}
case 1:
{
lean_object* v___x_6256_; 
v___x_6256_ = lean_unsigned_to_nat(1u);
return v___x_6256_;
}
default: 
{
lean_object* v___x_6257_; 
v___x_6257_ = lean_unsigned_to_nat(2u);
return v___x_6257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6258_){
_start:
{
uint8_t v_x_boxed_6259_; lean_object* v_res_6260_; 
v_x_boxed_6259_ = lean_unbox(v_x_6258_);
v_res_6260_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6259_);
return v_res_6260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t v_x_6261_){
_start:
{
lean_object* v___x_6262_; 
v___x_6262_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_6261_);
return v___x_6262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object* v_x_6263_){
_start:
{
uint8_t v_x_4__boxed_6264_; lean_object* v_res_6265_; 
v_x_4__boxed_6264_ = lean_unbox(v_x_6263_);
v_res_6265_ = l_Lean_Meta_ApplyNewGoals_toCtorIdx(v_x_4__boxed_6264_);
return v_res_6265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6266_){
_start:
{
lean_inc(v_k_6266_);
return v_k_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6267_){
_start:
{
lean_object* v_res_6268_; 
v_res_6268_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6267_);
lean_dec(v_k_6267_);
return v_res_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6269_, lean_object* v_ctorIdx_6270_, uint8_t v_t_6271_, lean_object* v_h_6272_, lean_object* v_k_6273_){
_start:
{
lean_inc(v_k_6273_);
return v_k_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6274_, lean_object* v_ctorIdx_6275_, lean_object* v_t_6276_, lean_object* v_h_6277_, lean_object* v_k_6278_){
_start:
{
uint8_t v_t_boxed_6279_; lean_object* v_res_6280_; 
v_t_boxed_6279_ = lean_unbox(v_t_6276_);
v_res_6280_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6274_, v_ctorIdx_6275_, v_t_boxed_6279_, v_h_6277_, v_k_6278_);
lean_dec(v_k_6278_);
lean_dec(v_ctorIdx_6275_);
return v_res_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6281_){
_start:
{
lean_inc(v_nonDependentFirst_6281_);
return v_nonDependentFirst_6281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6282_);
lean_dec(v_nonDependentFirst_6282_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6284_, uint8_t v_t_6285_, lean_object* v_h_6286_, lean_object* v_nonDependentFirst_6287_){
_start:
{
lean_inc(v_nonDependentFirst_6287_);
return v_nonDependentFirst_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6288_, lean_object* v_t_6289_, lean_object* v_h_6290_, lean_object* v_nonDependentFirst_6291_){
_start:
{
uint8_t v_t_boxed_6292_; lean_object* v_res_6293_; 
v_t_boxed_6292_ = lean_unbox(v_t_6289_);
v_res_6293_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6288_, v_t_boxed_6292_, v_h_6290_, v_nonDependentFirst_6291_);
lean_dec(v_nonDependentFirst_6291_);
return v_res_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6294_){
_start:
{
lean_inc(v_nonDependentOnly_6294_);
return v_nonDependentOnly_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6295_){
_start:
{
lean_object* v_res_6296_; 
v_res_6296_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6295_);
lean_dec(v_nonDependentOnly_6295_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6297_, uint8_t v_t_6298_, lean_object* v_h_6299_, lean_object* v_nonDependentOnly_6300_){
_start:
{
lean_inc(v_nonDependentOnly_6300_);
return v_nonDependentOnly_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6301_, lean_object* v_t_6302_, lean_object* v_h_6303_, lean_object* v_nonDependentOnly_6304_){
_start:
{
uint8_t v_t_boxed_6305_; lean_object* v_res_6306_; 
v_t_boxed_6305_ = lean_unbox(v_t_6302_);
v_res_6306_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6301_, v_t_boxed_6305_, v_h_6303_, v_nonDependentOnly_6304_);
lean_dec(v_nonDependentOnly_6304_);
return v_res_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6307_){
_start:
{
lean_inc(v_all_6307_);
return v_all_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6308_){
_start:
{
lean_object* v_res_6309_; 
v_res_6309_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6308_);
lean_dec(v_all_6308_);
return v_res_6309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6310_, uint8_t v_t_6311_, lean_object* v_h_6312_, lean_object* v_all_6313_){
_start:
{
lean_inc(v_all_6313_);
return v_all_6313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6314_, lean_object* v_t_6315_, lean_object* v_h_6316_, lean_object* v_all_6317_){
_start:
{
uint8_t v_t_boxed_6318_; lean_object* v_res_6319_; 
v_t_boxed_6318_ = lean_unbox(v_t_6315_);
v_res_6319_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6314_, v_t_boxed_6318_, v_h_6316_, v_all_6317_);
lean_dec(v_all_6317_);
return v_res_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6333_){
_start:
{
lean_object* v___x_6334_; uint8_t v___x_6335_; 
v___x_6334_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6333_);
v___x_6335_ = l_Lean_Syntax_isOfKind(v_c_6333_, v___x_6334_);
if (v___x_6335_ == 0)
{
lean_object* v___x_6336_; uint8_t v___x_6337_; 
v___x_6336_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6333_);
v___x_6337_ = l_Lean_Syntax_isOfKind(v_c_6333_, v___x_6336_);
if (v___x_6337_ == 0)
{
lean_object* v___x_6338_; uint8_t v___x_6339_; 
v___x_6338_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6333_);
v___x_6339_ = l_Lean_Syntax_isOfKind(v_c_6333_, v___x_6338_);
if (v___x_6339_ == 0)
{
lean_object* v___x_6340_; 
lean_dec(v_c_6333_);
v___x_6340_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6340_;
}
else
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6341_ = lean_unsigned_to_nat(1u);
v___x_6342_ = lean_mk_empty_array_with_capacity(v___x_6341_);
v___x_6343_ = lean_array_push(v___x_6342_, v_c_6333_);
return v___x_6343_;
}
}
else
{
lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; 
v___x_6344_ = lean_unsigned_to_nat(0u);
v___x_6345_ = l_Lean_Syntax_getArg(v_c_6333_, v___x_6344_);
lean_dec(v_c_6333_);
v___x_6346_ = l_Lean_Syntax_getArgs(v___x_6345_);
lean_dec(v___x_6345_);
return v___x_6346_;
}
}
else
{
lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; uint8_t v___x_6351_; 
v___x_6347_ = l_Lean_Syntax_getArgs(v_c_6333_);
lean_dec(v_c_6333_);
v___x_6348_ = lean_unsigned_to_nat(0u);
v___x_6349_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6350_ = lean_array_get_size(v___x_6347_);
v___x_6351_ = lean_nat_dec_lt(v___x_6348_, v___x_6350_);
if (v___x_6351_ == 0)
{
lean_dec_ref(v___x_6347_);
return v___x_6349_;
}
else
{
uint8_t v___x_6352_; 
v___x_6352_ = lean_nat_dec_le(v___x_6350_, v___x_6350_);
if (v___x_6352_ == 0)
{
if (v___x_6351_ == 0)
{
lean_dec_ref(v___x_6347_);
return v___x_6349_;
}
else
{
size_t v___x_6353_; size_t v___x_6354_; lean_object* v___x_6355_; 
v___x_6353_ = ((size_t)0ULL);
v___x_6354_ = lean_usize_of_nat(v___x_6350_);
v___x_6355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6347_, v___x_6353_, v___x_6354_, v___x_6349_);
lean_dec_ref(v___x_6347_);
return v___x_6355_;
}
}
else
{
size_t v___x_6356_; size_t v___x_6357_; lean_object* v___x_6358_; 
v___x_6356_ = ((size_t)0ULL);
v___x_6357_ = lean_usize_of_nat(v___x_6350_);
v___x_6358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6347_, v___x_6356_, v___x_6357_, v___x_6349_);
lean_dec_ref(v___x_6347_);
return v___x_6358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6359_, size_t v_i_6360_, size_t v_stop_6361_, lean_object* v_b_6362_){
_start:
{
uint8_t v___x_6363_; 
v___x_6363_ = lean_usize_dec_eq(v_i_6360_, v_stop_6361_);
if (v___x_6363_ == 0)
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; size_t v___x_6367_; size_t v___x_6368_; 
v___x_6364_ = lean_array_uget_borrowed(v_as_6359_, v_i_6360_);
lean_inc(v___x_6364_);
v___x_6365_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6364_);
v___x_6366_ = l_Array_append___redArg(v_b_6362_, v___x_6365_);
lean_dec_ref(v___x_6365_);
v___x_6367_ = ((size_t)1ULL);
v___x_6368_ = lean_usize_add(v_i_6360_, v___x_6367_);
v_i_6360_ = v___x_6368_;
v_b_6362_ = v___x_6366_;
goto _start;
}
else
{
return v_b_6362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6370_, lean_object* v_i_6371_, lean_object* v_stop_6372_, lean_object* v_b_6373_){
_start:
{
size_t v_i_boxed_6374_; size_t v_stop_boxed_6375_; lean_object* v_res_6376_; 
v_i_boxed_6374_ = lean_unbox_usize(v_i_6371_);
lean_dec(v_i_6371_);
v_stop_boxed_6375_ = lean_unbox_usize(v_stop_6372_);
lean_dec(v_stop_6372_);
v_res_6376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6370_, v_i_boxed_6374_, v_stop_boxed_6375_, v_b_6373_);
lean_dec_ref(v_as_6370_);
return v_res_6376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6377_){
_start:
{
lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6378_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6379_ = lean_box(2);
v___x_6380_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6381_, 0, v___x_6379_);
lean_ctor_set(v___x_6381_, 1, v___x_6380_);
lean_ctor_set(v___x_6381_, 2, v_items_6377_);
v___x_6382_ = l_Lean_Syntax_node1(v___x_6379_, v___x_6378_, v___x_6381_);
return v___x_6382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6383_, lean_object* v_cfg_x27_6384_){
_start:
{
lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6385_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6383_);
v___x_6386_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6384_);
v___x_6387_ = l_Array_append___redArg(v___x_6385_, v___x_6386_);
lean_dec_ref(v___x_6386_);
v___x_6388_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6387_);
return v___x_6388_;
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
