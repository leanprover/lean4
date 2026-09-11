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
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object* v_sep_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(v___x_2749_, 0, v_sep_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2750_, lean_object* v_elems_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2750_, v_elems_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2753_, lean_object* v_elems_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2753_, v_elems_2754_);
lean_dec_ref(v_elems_2754_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2756_, lean_object* v_sep_2757_, lean_object* v_elems_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2757_, v_elems_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2760_, lean_object* v_sep_2761_, lean_object* v_elems_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2760_, v_sep_2761_, v_elems_2762_);
lean_dec_ref(v_elems_2762_);
lean_dec(v_k_2760_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2764_, lean_object* v_sep_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2766_, 0, v_k_2764_);
lean_closure_set(v___x_2766_, 1, v_sep_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = lean_array_get_size(v_x_2774_);
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_nat_dec_eq(v___x_2775_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2778_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2779_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2780_ = lean_box(2);
v___x_2781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v___x_2779_);
lean_ctor_set(v___x_2781_, 2, v_x_2774_);
v___x_2782_ = lean_unsigned_to_nat(2u);
v___x_2783_ = lean_mk_empty_array_with_capacity(v___x_2782_);
v___x_2784_ = lean_array_push(v___x_2783_, v_fn_2773_);
v___x_2785_ = lean_array_push(v___x_2784_, v___x_2781_);
v___x_2786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2780_);
lean_ctor_set(v___x_2786_, 1, v___x_2778_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
return v___x_2786_;
}
else
{
lean_dec_ref(v_x_2774_);
return v_fn_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2787_, lean_object* v_args_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = l_Lean_mkCIdent(v_fn_2787_);
v___x_2790_ = l_Lean_Syntax_mkApp(v___x_2789_, v_args_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2791_, lean_object* v_val_2792_, lean_object* v_info_2793_){
_start:
{
lean_object* v_atom_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_atom_2794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2794_, 0, v_info_2793_);
lean_ctor_set(v_atom_2794_, 1, v_val_2792_);
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = lean_mk_empty_array_with_capacity(v___x_2795_);
v___x_2797_ = lean_array_push(v___x_2796_, v_atom_2794_);
v___x_2798_ = lean_box(2);
v___x_2799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_kind_2791_);
lean_ctor_set(v___x_2799_, 2, v___x_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2803_, lean_object* v_info_2804_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2806_ = l_Char_quote(v_val_2803_);
v___x_2807_ = l_Lean_Syntax_mkLit(v___x_2805_, v___x_2806_, v_info_2804_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2808_, lean_object* v_info_2809_){
_start:
{
uint32_t v_val_boxed_2810_; lean_object* v_res_2811_; 
v_val_boxed_2810_ = lean_unbox_uint32(v_val_2808_);
lean_dec(v_val_2808_);
v_res_2811_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2810_, v_info_2809_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2815_, lean_object* v_info_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2818_ = l_String_quote(v_val_2815_);
v___x_2819_ = l_Lean_Syntax_mkLit(v___x_2817_, v___x_2818_, v_info_2816_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2823_, lean_object* v_info_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2826_ = l_Lean_Syntax_mkLit(v___x_2825_, v_val_2823_, v_info_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2827_, lean_object* v_info_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2830_ = l_Nat_reprFast(v_val_2827_);
v___x_2831_ = l_Lean_Syntax_mkLit(v___x_2829_, v___x_2830_, v_info_2828_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2835_, lean_object* v_info_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2838_ = l_Lean_Syntax_mkLit(v___x_2837_, v_val_2835_, v_info_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2842_, lean_object* v_info_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2845_ = l_Lean_Syntax_mkLit(v___x_2844_, v_val_2842_, v_info_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2846_, lean_object* v_i_2847_, lean_object* v_val_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_string_utf8_at_end(v_s_2846_, v_i_2847_);
if (v___x_2849_ == 0)
{
uint32_t v_c_2850_; uint32_t v___x_2851_; uint8_t v___x_2852_; 
v_c_2850_ = lean_string_utf8_get(v_s_2846_, v_i_2847_);
v___x_2851_ = 48;
v___x_2852_ = lean_uint32_dec_eq(v_c_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
uint32_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2853_ = 49;
v___x_2854_ = lean_uint32_dec_eq(v_c_2850_, v___x_2853_);
if (v___x_2854_ == 0)
{
uint32_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = 95;
v___x_2856_ = lean_uint32_dec_eq(v_c_2850_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec(v_val_2848_);
lean_dec(v_i_2847_);
v___x_2857_ = lean_box(0);
return v___x_2857_;
}
else
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_string_utf8_next(v_s_2846_, v_i_2847_);
lean_dec(v_i_2847_);
v_i_2847_ = v___x_2858_;
goto _start;
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2860_ = lean_string_utf8_next(v_s_2846_, v_i_2847_);
lean_dec(v_i_2847_);
v___x_2861_ = lean_unsigned_to_nat(2u);
v___x_2862_ = lean_nat_mul(v___x_2861_, v_val_2848_);
lean_dec(v_val_2848_);
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_nat_add(v___x_2862_, v___x_2863_);
lean_dec(v___x_2862_);
v_i_2847_ = v___x_2860_;
v_val_2848_ = v___x_2864_;
goto _start;
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2866_ = lean_string_utf8_next(v_s_2846_, v_i_2847_);
lean_dec(v_i_2847_);
v___x_2867_ = lean_unsigned_to_nat(2u);
v___x_2868_ = lean_nat_mul(v___x_2867_, v_val_2848_);
lean_dec(v_val_2848_);
v_i_2847_ = v___x_2866_;
v_val_2848_ = v___x_2868_;
goto _start;
}
}
else
{
lean_object* v___x_2870_; 
lean_dec(v_i_2847_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_val_2848_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2871_, lean_object* v_i_2872_, lean_object* v_val_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2871_, v_i_2872_, v_val_2873_);
lean_dec_ref(v_s_2871_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2875_, lean_object* v_i_2876_, lean_object* v_val_2877_){
_start:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_string_utf8_at_end(v_s_2875_, v_i_2876_);
if (v___x_2878_ == 0)
{
uint32_t v_c_2879_; uint8_t v___y_2881_; uint32_t v___x_2895_; uint8_t v___x_2896_; 
v_c_2879_ = lean_string_utf8_get(v_s_2875_, v_i_2876_);
v___x_2895_ = 48;
v___x_2896_ = lean_uint32_dec_le(v___x_2895_, v_c_2879_);
if (v___x_2896_ == 0)
{
v___y_2881_ = v___x_2878_;
goto v___jp_2880_;
}
else
{
uint32_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = 55;
v___x_2898_ = lean_uint32_dec_le(v_c_2879_, v___x_2897_);
v___y_2881_ = v___x_2898_;
goto v___jp_2880_;
}
v___jp_2880_:
{
if (v___y_2881_ == 0)
{
uint32_t v___x_2882_; uint8_t v___x_2883_; 
v___x_2882_ = 95;
v___x_2883_ = lean_uint32_dec_eq(v_c_2879_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec(v_val_2877_);
lean_dec(v_i_2876_);
v___x_2884_ = lean_box(0);
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_string_utf8_next(v_s_2875_, v_i_2876_);
lean_dec(v_i_2876_);
v_i_2876_ = v___x_2885_;
goto _start;
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2887_ = lean_string_utf8_next(v_s_2875_, v_i_2876_);
lean_dec(v_i_2876_);
v___x_2888_ = lean_unsigned_to_nat(8u);
v___x_2889_ = lean_nat_mul(v___x_2888_, v_val_2877_);
lean_dec(v_val_2877_);
v___x_2890_ = lean_uint32_to_nat(v_c_2879_);
v___x_2891_ = lean_nat_add(v___x_2889_, v___x_2890_);
lean_dec(v___x_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_unsigned_to_nat(48u);
v___x_2893_ = lean_nat_sub(v___x_2891_, v___x_2892_);
lean_dec(v___x_2891_);
v_i_2876_ = v___x_2887_;
v_val_2877_ = v___x_2893_;
goto _start;
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec(v_i_2876_);
v___x_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2899_, 0, v_val_2877_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2900_, lean_object* v_i_2901_, lean_object* v_val_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2900_, v_i_2901_, v_val_2902_);
lean_dec_ref(v_s_2900_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2904_, lean_object* v_i_2905_){
_start:
{
uint32_t v_c_2906_; lean_object* v_i_2907_; uint32_t v___x_2934_; uint8_t v___x_2935_; 
v_c_2906_ = lean_string_utf8_get(v_s_2904_, v_i_2905_);
v_i_2907_ = lean_string_utf8_next(v_s_2904_, v_i_2905_);
v___x_2934_ = 48;
v___x_2935_ = lean_uint32_dec_le(v___x_2934_, v_c_2906_);
if (v___x_2935_ == 0)
{
goto v___jp_2922_;
}
else
{
uint32_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = 57;
v___x_2937_ = lean_uint32_dec_le(v_c_2906_, v___x_2936_);
if (v___x_2937_ == 0)
{
goto v___jp_2922_;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2938_ = lean_uint32_to_nat(v_c_2906_);
v___x_2939_ = lean_unsigned_to_nat(48u);
v___x_2940_ = lean_nat_sub(v___x_2938_, v___x_2939_);
lean_dec(v___x_2938_);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_i_2907_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
v___jp_2908_:
{
uint32_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = 65;
v___x_2910_ = lean_uint32_dec_le(v___x_2909_, v_c_2906_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_dec(v_i_2907_);
v___x_2911_ = lean_box(0);
return v___x_2911_;
}
else
{
uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = 70;
v___x_2913_ = lean_uint32_dec_le(v_c_2906_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; 
lean_dec(v_i_2907_);
v___x_2914_ = lean_box(0);
return v___x_2914_;
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2915_ = lean_unsigned_to_nat(10u);
v___x_2916_ = lean_uint32_to_nat(v_c_2906_);
v___x_2917_ = lean_nat_add(v___x_2915_, v___x_2916_);
lean_dec(v___x_2916_);
v___x_2918_ = lean_unsigned_to_nat(65u);
v___x_2919_ = lean_nat_sub(v___x_2917_, v___x_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set(v___x_2920_, 1, v_i_2907_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
}
v___jp_2922_:
{
uint32_t v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = 97;
v___x_2924_ = lean_uint32_dec_le(v___x_2923_, v_c_2906_);
if (v___x_2924_ == 0)
{
goto v___jp_2908_;
}
else
{
uint32_t v___x_2925_; uint8_t v___x_2926_; 
v___x_2925_ = 102;
v___x_2926_ = lean_uint32_dec_le(v_c_2906_, v___x_2925_);
if (v___x_2926_ == 0)
{
goto v___jp_2908_;
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2927_ = lean_unsigned_to_nat(10u);
v___x_2928_ = lean_uint32_to_nat(v_c_2906_);
v___x_2929_ = lean_nat_add(v___x_2927_, v___x_2928_);
lean_dec(v___x_2928_);
v___x_2930_ = lean_unsigned_to_nat(97u);
v___x_2931_ = lean_nat_sub(v___x_2929_, v___x_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_ctor_set(v___x_2932_, 1, v_i_2907_);
v___x_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
return v___x_2933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2943_, lean_object* v_i_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2943_, v_i_2944_);
lean_dec(v_i_2944_);
lean_dec_ref(v_s_2943_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2946_, lean_object* v_i_2947_, lean_object* v_val_2948_){
_start:
{
uint8_t v___x_2949_; 
v___x_2949_ = lean_string_utf8_at_end(v_s_2946_, v_i_2947_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2946_, v_i_2947_);
if (lean_obj_tag(v___x_2950_) == 0)
{
uint32_t v___x_2951_; uint32_t v___x_2952_; uint8_t v___x_2953_; 
v___x_2951_ = lean_string_utf8_get(v_s_2946_, v_i_2947_);
v___x_2952_ = 95;
v___x_2953_ = lean_uint32_dec_eq(v___x_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_val_2948_);
lean_dec(v_i_2947_);
v___x_2954_ = lean_box(0);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_string_utf8_next(v_s_2946_, v_i_2947_);
lean_dec(v_i_2947_);
v_i_2947_ = v___x_2955_;
goto _start;
}
}
else
{
lean_object* v_val_2957_; lean_object* v_fst_2958_; lean_object* v_snd_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_dec(v_i_2947_);
v_val_2957_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v___x_2950_, 1);
v_fst_2958_ = lean_ctor_get(v_val_2957_, 0);
lean_inc(v_fst_2958_);
v_snd_2959_ = lean_ctor_get(v_val_2957_, 1);
lean_inc(v_snd_2959_);
lean_dec(v_val_2957_);
v___x_2960_ = lean_unsigned_to_nat(16u);
v___x_2961_ = lean_nat_mul(v___x_2960_, v_val_2948_);
lean_dec(v_val_2948_);
v___x_2962_ = lean_nat_add(v___x_2961_, v_fst_2958_);
lean_dec(v_fst_2958_);
lean_dec(v___x_2961_);
v_i_2947_ = v_snd_2959_;
v_val_2948_ = v___x_2962_;
goto _start;
}
}
else
{
lean_object* v___x_2964_; 
lean_dec(v_i_2947_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v_val_2948_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_2965_, lean_object* v_i_2966_, lean_object* v_val_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2965_, v_i_2966_, v_val_2967_);
lean_dec_ref(v_s_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_2969_, lean_object* v_i_2970_, lean_object* v_val_2971_){
_start:
{
uint8_t v___x_2972_; 
v___x_2972_ = lean_string_utf8_at_end(v_s_2969_, v_i_2970_);
if (v___x_2972_ == 0)
{
uint32_t v_c_2973_; uint8_t v___y_2975_; uint32_t v___x_2989_; uint8_t v___x_2990_; 
v_c_2973_ = lean_string_utf8_get(v_s_2969_, v_i_2970_);
v___x_2989_ = 48;
v___x_2990_ = lean_uint32_dec_le(v___x_2989_, v_c_2973_);
if (v___x_2990_ == 0)
{
v___y_2975_ = v___x_2972_;
goto v___jp_2974_;
}
else
{
uint32_t v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = 57;
v___x_2992_ = lean_uint32_dec_le(v_c_2973_, v___x_2991_);
v___y_2975_ = v___x_2992_;
goto v___jp_2974_;
}
v___jp_2974_:
{
if (v___y_2975_ == 0)
{
uint32_t v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = 95;
v___x_2977_ = lean_uint32_dec_eq(v_c_2973_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_val_2971_);
lean_dec(v_i_2970_);
v___x_2978_ = lean_box(0);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_string_utf8_next(v_s_2969_, v_i_2970_);
lean_dec(v_i_2970_);
v_i_2970_ = v___x_2979_;
goto _start;
}
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2981_ = lean_string_utf8_next(v_s_2969_, v_i_2970_);
lean_dec(v_i_2970_);
v___x_2982_ = lean_unsigned_to_nat(10u);
v___x_2983_ = lean_nat_mul(v___x_2982_, v_val_2971_);
lean_dec(v_val_2971_);
v___x_2984_ = lean_uint32_to_nat(v_c_2973_);
v___x_2985_ = lean_nat_add(v___x_2983_, v___x_2984_);
lean_dec(v___x_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_unsigned_to_nat(48u);
v___x_2987_ = lean_nat_sub(v___x_2985_, v___x_2986_);
lean_dec(v___x_2985_);
v_i_2970_ = v___x_2981_;
v_val_2971_ = v___x_2987_;
goto _start;
}
}
}
else
{
lean_object* v___x_2993_; 
lean_dec(v_i_2970_);
v___x_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2993_, 0, v_val_2971_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_2994_, lean_object* v_i_2995_, lean_object* v_val_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2994_, v_i_2995_, v_val_2996_);
lean_dec_ref(v_s_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3000_){
_start:
{
lean_object* v_len_3001_; lean_object* v___x_3002_; uint8_t v___x_3012_; 
v_len_3001_ = lean_string_length(v_s_3000_);
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_nat_dec_eq(v_len_3001_, v___x_3002_);
if (v___x_3012_ == 0)
{
uint32_t v_c_3013_; uint32_t v___x_3014_; uint8_t v___x_3015_; 
v_c_3013_ = lean_string_utf8_get(v_s_3000_, v___x_3002_);
v___x_3014_ = 48;
v___x_3015_ = lean_uint32_dec_eq(v_c_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
uint8_t v___x_3016_; 
lean_dec(v_len_3001_);
v___x_3016_ = lean_uint32_dec_le(v___x_3014_, v_c_3013_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_box(0);
return v___x_3017_;
}
else
{
uint32_t v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = 57;
v___x_3019_ = lean_uint32_dec_le(v_c_3013_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_box(0);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3000_, v___x_3002_, v___x_3002_);
return v___x_3021_;
}
}
}
else
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = lean_unsigned_to_nat(1u);
v___x_3023_ = lean_nat_dec_eq(v_len_3001_, v___x_3022_);
lean_dec(v_len_3001_);
if (v___x_3023_ == 0)
{
uint32_t v_c_3024_; uint32_t v___x_3025_; uint8_t v___x_3026_; 
v_c_3024_ = lean_string_utf8_get(v_s_3000_, v___x_3022_);
v___x_3025_ = 120;
v___x_3026_ = lean_uint32_dec_eq(v_c_3024_, v___x_3025_);
if (v___x_3026_ == 0)
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 88;
v___x_3028_ = lean_uint32_dec_eq(v_c_3024_, v___x_3027_);
if (v___x_3028_ == 0)
{
uint32_t v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = 98;
v___x_3030_ = lean_uint32_dec_eq(v_c_3024_, v___x_3029_);
if (v___x_3030_ == 0)
{
uint32_t v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = 66;
v___x_3032_ = lean_uint32_dec_eq(v_c_3024_, v___x_3031_);
if (v___x_3032_ == 0)
{
uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = 111;
v___x_3034_ = lean_uint32_dec_eq(v_c_3024_, v___x_3033_);
if (v___x_3034_ == 0)
{
uint32_t v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = 79;
v___x_3036_ = lean_uint32_dec_eq(v_c_3024_, v___x_3035_);
if (v___x_3036_ == 0)
{
uint8_t v___x_3037_; 
v___x_3037_ = lean_uint32_dec_le(v___x_3014_, v_c_3024_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_box(0);
return v___x_3038_;
}
else
{
uint32_t v___x_3039_; uint8_t v___x_3040_; 
v___x_3039_ = 57;
v___x_3040_ = lean_uint32_dec_le(v_c_3024_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_box(0);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3000_, v___x_3002_, v___x_3002_);
return v___x_3042_;
}
}
}
else
{
goto v___jp_3003_;
}
}
else
{
goto v___jp_3003_;
}
}
else
{
goto v___jp_3006_;
}
}
else
{
goto v___jp_3006_;
}
}
else
{
goto v___jp_3009_;
}
}
else
{
goto v___jp_3009_;
}
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3043_;
}
}
}
else
{
lean_object* v___x_3044_; 
lean_dec(v_len_3001_);
v___x_3044_ = lean_box(0);
return v___x_3044_;
}
v___jp_3003_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_unsigned_to_nat(2u);
v___x_3005_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3000_, v___x_3004_, v___x_3002_);
return v___x_3005_;
}
v___jp_3006_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_unsigned_to_nat(2u);
v___x_3008_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3000_, v___x_3007_, v___x_3002_);
return v___x_3008_;
}
v___jp_3009_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_unsigned_to_nat(2u);
v___x_3011_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3000_, v___x_3010_, v___x_3002_);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3045_);
lean_dec_ref(v_s_3045_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3047_, lean_object* v_stx_3048_){
_start:
{
if (lean_obj_tag(v_stx_3048_) == 1)
{
lean_object* v_kind_3049_; lean_object* v_args_3050_; uint8_t v___y_3052_; uint8_t v___x_3059_; 
v_kind_3049_ = lean_ctor_get(v_stx_3048_, 1);
v_args_3050_ = lean_ctor_get(v_stx_3048_, 2);
v___x_3059_ = lean_name_eq(v_kind_3049_, v_litKind_3047_);
if (v___x_3059_ == 0)
{
v___y_3052_ = v___x_3059_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3060_ = lean_array_get_size(v_args_3050_);
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_dec_eq(v___x_3060_, v___x_3061_);
v___y_3052_ = v___x_3062_;
goto v___jp_3051_;
}
v___jp_3051_:
{
if (v___y_3052_ == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_box(0);
return v___x_3053_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = lean_array_fget_borrowed(v_args_3050_, v___x_3054_);
if (lean_obj_tag(v___x_3055_) == 2)
{
lean_object* v_val_3056_; lean_object* v___x_3057_; 
v_val_3056_ = lean_ctor_get(v___x_3055_, 1);
lean_inc_ref(v_val_3056_);
v___x_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_val_3056_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_box(0);
return v___x_3058_;
}
}
}
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3064_, lean_object* v_stx_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Syntax_isLit_x3f(v_litKind_3064_, v_stx_3065_);
lean_dec(v_stx_3065_);
lean_dec(v_litKind_3064_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3067_, lean_object* v_stx_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Syntax_isLit_x3f(v_litKind_3067_, v_stx_3068_);
if (lean_obj_tag(v___x_3069_) == 1)
{
lean_object* v_val_3070_; lean_object* v___x_3071_; 
v_val_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_val_3070_);
lean_dec_ref_known(v___x_3069_, 1);
v___x_3071_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3070_);
lean_dec(v_val_3070_);
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; 
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
return v___x_3072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3073_, lean_object* v_stx_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3073_, v_stx_3074_);
lean_dec(v_stx_3074_);
lean_dec(v_litKind_3073_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3076_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3078_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3077_, v_s_3076_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_Syntax_isNatLit_x3f(v_s_3079_);
lean_dec(v_s_3079_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3086_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3085_, v_s_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3087_);
lean_dec(v_s_3087_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3089_, lean_object* v_i_3090_, lean_object* v_val_3091_, lean_object* v_e_3092_, uint8_t v_sign_3093_, lean_object* v_exp_3094_){
_start:
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_string_utf8_at_end(v_s_3089_, v_i_3090_);
if (v___x_3095_ == 0)
{
uint32_t v_c_3096_; uint8_t v___y_3098_; uint32_t v___x_3112_; uint8_t v___x_3113_; 
v_c_3096_ = lean_string_utf8_get(v_s_3089_, v_i_3090_);
v___x_3112_ = 48;
v___x_3113_ = lean_uint32_dec_le(v___x_3112_, v_c_3096_);
if (v___x_3113_ == 0)
{
v___y_3098_ = v___x_3095_;
goto v___jp_3097_;
}
else
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 57;
v___x_3115_ = lean_uint32_dec_le(v_c_3096_, v___x_3114_);
v___y_3098_ = v___x_3115_;
goto v___jp_3097_;
}
v___jp_3097_:
{
if (v___y_3098_ == 0)
{
uint32_t v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = 95;
v___x_3100_ = lean_uint32_dec_eq(v_c_3096_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_dec(v_exp_3094_);
lean_dec(v_val_3091_);
lean_dec(v_i_3090_);
v___x_3101_ = lean_box(0);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = lean_string_utf8_next(v_s_3089_, v_i_3090_);
lean_dec(v_i_3090_);
v_i_3090_ = v___x_3102_;
goto _start;
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3104_ = lean_string_utf8_next(v_s_3089_, v_i_3090_);
lean_dec(v_i_3090_);
v___x_3105_ = lean_unsigned_to_nat(10u);
v___x_3106_ = lean_nat_mul(v___x_3105_, v_exp_3094_);
lean_dec(v_exp_3094_);
v___x_3107_ = lean_uint32_to_nat(v_c_3096_);
v___x_3108_ = lean_nat_add(v___x_3106_, v___x_3107_);
lean_dec(v___x_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_unsigned_to_nat(48u);
v___x_3110_ = lean_nat_sub(v___x_3108_, v___x_3109_);
lean_dec(v___x_3108_);
v_i_3090_ = v___x_3104_;
v_exp_3094_ = v___x_3110_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3090_);
if (v_sign_3093_ == 0)
{
uint8_t v___x_3116_; 
v___x_3116_ = lean_nat_dec_le(v_e_3092_, v_exp_3094_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3117_ = lean_nat_sub(v_e_3092_, v_exp_3094_);
lean_dec(v_exp_3094_);
v___x_3118_ = lean_box(v___x_3095_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___x_3117_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v_val_3091_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3122_ = lean_nat_sub(v_exp_3094_, v_e_3092_);
lean_dec(v_exp_3094_);
v___x_3123_ = lean_box(v_sign_3093_);
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v___x_3122_);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_val_3091_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3127_ = lean_nat_add(v_exp_3094_, v_e_3092_);
lean_dec(v_exp_3094_);
v___x_3128_ = lean_box(v_sign_3093_);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v___x_3127_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_val_3091_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3132_, lean_object* v_i_3133_, lean_object* v_val_3134_, lean_object* v_e_3135_, lean_object* v_sign_3136_, lean_object* v_exp_3137_){
_start:
{
uint8_t v_sign_boxed_3138_; lean_object* v_res_3139_; 
v_sign_boxed_3138_ = lean_unbox(v_sign_3136_);
v_res_3139_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3132_, v_i_3133_, v_val_3134_, v_e_3135_, v_sign_boxed_3138_, v_exp_3137_);
lean_dec(v_e_3135_);
lean_dec_ref(v_s_3132_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3140_, lean_object* v_i_3141_, lean_object* v_val_3142_, lean_object* v_e_3143_){
_start:
{
uint8_t v___x_3144_; 
v___x_3144_ = lean_string_utf8_at_end(v_s_3140_, v_i_3141_);
if (v___x_3144_ == 0)
{
uint32_t v_c_3145_; uint32_t v___x_3146_; uint8_t v___x_3147_; 
v_c_3145_ = lean_string_utf8_get(v_s_3140_, v_i_3141_);
v___x_3146_ = 45;
v___x_3147_ = lean_uint32_dec_eq(v_c_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
uint32_t v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = 43;
v___x_3149_ = lean_uint32_dec_eq(v_c_3145_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3140_, v_i_3141_, v_val_3142_, v_e_3143_, v___x_3149_, v___x_3150_);
return v___x_3151_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_string_utf8_next(v_s_3140_, v_i_3141_);
lean_dec(v_i_3141_);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3140_, v___x_3152_, v_val_3142_, v_e_3143_, v___x_3147_, v___x_3153_);
return v___x_3154_;
}
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_string_utf8_next(v_s_3140_, v_i_3141_);
lean_dec(v_i_3141_);
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3140_, v___x_3155_, v_val_3142_, v_e_3143_, v___x_3147_, v___x_3156_);
return v___x_3157_;
}
}
else
{
lean_object* v___x_3158_; 
lean_dec(v_val_3142_);
lean_dec(v_i_3141_);
v___x_3158_ = lean_box(0);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3159_, lean_object* v_i_3160_, lean_object* v_val_3161_, lean_object* v_e_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3159_, v_i_3160_, v_val_3161_, v_e_3162_);
lean_dec(v_e_3162_);
lean_dec_ref(v_s_3159_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3164_, lean_object* v_i_3165_, lean_object* v_val_3166_, lean_object* v_e_3167_){
_start:
{
uint8_t v___x_3171_; 
v___x_3171_ = lean_string_utf8_at_end(v_s_3164_, v_i_3165_);
if (v___x_3171_ == 0)
{
uint32_t v_c_3172_; uint8_t v___y_3174_; uint32_t v___x_3194_; uint8_t v___x_3195_; 
v_c_3172_ = lean_string_utf8_get(v_s_3164_, v_i_3165_);
v___x_3194_ = 48;
v___x_3195_ = lean_uint32_dec_le(v___x_3194_, v_c_3172_);
if (v___x_3195_ == 0)
{
v___y_3174_ = v___x_3171_;
goto v___jp_3173_;
}
else
{
uint32_t v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = 57;
v___x_3197_ = lean_uint32_dec_le(v_c_3172_, v___x_3196_);
v___y_3174_ = v___x_3197_;
goto v___jp_3173_;
}
v___jp_3173_:
{
if (v___y_3174_ == 0)
{
uint32_t v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = 95;
v___x_3176_ = lean_uint32_dec_eq(v_c_3172_, v___x_3175_);
if (v___x_3176_ == 0)
{
uint32_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = 101;
v___x_3178_ = lean_uint32_dec_eq(v_c_3172_, v___x_3177_);
if (v___x_3178_ == 0)
{
uint32_t v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = 69;
v___x_3180_ = lean_uint32_dec_eq(v_c_3172_, v___x_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec(v_e_3167_);
lean_dec(v_val_3166_);
lean_dec(v_i_3165_);
v___x_3181_ = lean_box(0);
return v___x_3181_;
}
else
{
goto v___jp_3168_;
}
}
else
{
goto v___jp_3168_;
}
}
else
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_string_utf8_next(v_s_3164_, v_i_3165_);
lean_dec(v_i_3165_);
v_i_3165_ = v___x_3182_;
goto _start;
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3184_ = lean_string_utf8_next(v_s_3164_, v_i_3165_);
lean_dec(v_i_3165_);
v___x_3185_ = lean_unsigned_to_nat(10u);
v___x_3186_ = lean_nat_mul(v___x_3185_, v_val_3166_);
lean_dec(v_val_3166_);
v___x_3187_ = lean_uint32_to_nat(v_c_3172_);
v___x_3188_ = lean_nat_add(v___x_3186_, v___x_3187_);
lean_dec(v___x_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_unsigned_to_nat(48u);
v___x_3190_ = lean_nat_sub(v___x_3188_, v___x_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_unsigned_to_nat(1u);
v___x_3192_ = lean_nat_add(v_e_3167_, v___x_3191_);
lean_dec(v_e_3167_);
v_i_3165_ = v___x_3184_;
v_val_3166_ = v___x_3190_;
v_e_3167_ = v___x_3192_;
goto _start;
}
}
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec(v_i_3165_);
v___x_3198_ = lean_box(v___x_3171_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
lean_ctor_set(v___x_3199_, 1, v_e_3167_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_val_3166_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
v___jp_3168_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_string_utf8_next(v_s_3164_, v_i_3165_);
lean_dec(v_i_3165_);
v___x_3170_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3164_, v___x_3169_, v_val_3166_, v_e_3167_);
lean_dec(v_e_3167_);
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3202_, lean_object* v_i_3203_, lean_object* v_val_3204_, lean_object* v_e_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3202_, v_i_3203_, v_val_3204_, v_e_3205_);
lean_dec_ref(v_s_3202_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3207_, lean_object* v_i_3208_, lean_object* v_val_3209_){
_start:
{
uint8_t v___x_3214_; 
v___x_3214_ = lean_string_utf8_at_end(v_s_3207_, v_i_3208_);
if (v___x_3214_ == 0)
{
uint32_t v_c_3215_; uint8_t v___y_3217_; uint32_t v___x_3240_; uint8_t v___x_3241_; 
v_c_3215_ = lean_string_utf8_get(v_s_3207_, v_i_3208_);
v___x_3240_ = 48;
v___x_3241_ = lean_uint32_dec_le(v___x_3240_, v_c_3215_);
if (v___x_3241_ == 0)
{
v___y_3217_ = v___x_3214_;
goto v___jp_3216_;
}
else
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 57;
v___x_3243_ = lean_uint32_dec_le(v_c_3215_, v___x_3242_);
v___y_3217_ = v___x_3243_;
goto v___jp_3216_;
}
v___jp_3216_:
{
if (v___y_3217_ == 0)
{
uint32_t v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = 95;
v___x_3219_ = lean_uint32_dec_eq(v_c_3215_, v___x_3218_);
if (v___x_3219_ == 0)
{
uint32_t v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = 46;
v___x_3221_ = lean_uint32_dec_eq(v_c_3215_, v___x_3220_);
if (v___x_3221_ == 0)
{
uint32_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3222_ = 101;
v___x_3223_ = lean_uint32_dec_eq(v_c_3215_, v___x_3222_);
if (v___x_3223_ == 0)
{
uint32_t v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = 69;
v___x_3225_ = lean_uint32_dec_eq(v_c_3215_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; 
lean_dec(v_val_3209_);
lean_dec(v_i_3208_);
v___x_3226_ = lean_box(0);
return v___x_3226_;
}
else
{
goto v___jp_3210_;
}
}
else
{
goto v___jp_3210_;
}
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_string_utf8_next(v_s_3207_, v_i_3208_);
lean_dec(v_i_3208_);
v___x_3228_ = lean_unsigned_to_nat(0u);
v___x_3229_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3207_, v___x_3227_, v_val_3209_, v___x_3228_);
return v___x_3229_;
}
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_string_utf8_next(v_s_3207_, v_i_3208_);
lean_dec(v_i_3208_);
v_i_3208_ = v___x_3230_;
goto _start;
}
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3232_ = lean_string_utf8_next(v_s_3207_, v_i_3208_);
lean_dec(v_i_3208_);
v___x_3233_ = lean_unsigned_to_nat(10u);
v___x_3234_ = lean_nat_mul(v___x_3233_, v_val_3209_);
lean_dec(v_val_3209_);
v___x_3235_ = lean_uint32_to_nat(v_c_3215_);
v___x_3236_ = lean_nat_add(v___x_3234_, v___x_3235_);
lean_dec(v___x_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_unsigned_to_nat(48u);
v___x_3238_ = lean_nat_sub(v___x_3236_, v___x_3237_);
lean_dec(v___x_3236_);
v_i_3208_ = v___x_3232_;
v_val_3209_ = v___x_3238_;
goto _start;
}
}
}
else
{
lean_object* v___x_3244_; 
lean_dec(v_val_3209_);
lean_dec(v_i_3208_);
v___x_3244_ = lean_box(0);
return v___x_3244_;
}
v___jp_3210_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_string_utf8_next(v_s_3207_, v_i_3208_);
lean_dec(v_i_3208_);
v___x_3212_ = lean_unsigned_to_nat(0u);
v___x_3213_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3207_, v___x_3211_, v_val_3209_, v___x_3212_);
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3245_, lean_object* v_i_3246_, lean_object* v_val_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3245_, v_i_3246_, v_val_3247_);
lean_dec_ref(v_s_3245_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3249_){
_start:
{
lean_object* v_len_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v_len_3250_ = lean_string_length(v_s_3249_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_nat_dec_eq(v_len_3250_, v___x_3251_);
lean_dec(v_len_3250_);
if (v___x_3252_ == 0)
{
uint32_t v_c_3253_; uint32_t v___x_3254_; uint8_t v___x_3255_; 
v_c_3253_ = lean_string_utf8_get(v_s_3249_, v___x_3251_);
v___x_3254_ = 48;
v___x_3255_ = lean_uint32_dec_le(v___x_3254_, v_c_3253_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_box(0);
return v___x_3256_;
}
else
{
uint32_t v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = 57;
v___x_3258_ = lean_uint32_dec_le(v_c_3253_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_box(0);
return v___x_3259_;
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3249_, v___x_3251_, v___x_3251_);
return v___x_3260_;
}
}
}
else
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_box(0);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3262_);
lean_dec_ref(v_s_3262_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3264_){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3266_ = l_Lean_Syntax_isLit_x3f(v___x_3265_, v_stx_3264_);
if (lean_obj_tag(v___x_3266_) == 1)
{
lean_object* v_val_3267_; lean_object* v___x_3268_; 
v_val_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3267_);
lean_dec(v_val_3267_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; 
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3270_);
lean_dec(v_stx_3270_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3272_){
_start:
{
switch(lean_obj_tag(v_x_3272_))
{
case 2:
{
lean_object* v_val_3273_; lean_object* v___x_3274_; 
v_val_3273_ = lean_ctor_get(v_x_3272_, 1);
lean_inc_ref(v_val_3273_);
lean_dec_ref_known(v_x_3272_, 2);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_val_3273_);
return v___x_3274_;
}
case 3:
{
lean_object* v_rawVal_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_rawVal_3275_ = lean_ctor_get(v_x_3272_, 1);
lean_inc_ref(v_rawVal_3275_);
lean_dec_ref_known(v_x_3272_, 4);
v___x_3276_ = lean_substring_tostring(v_rawVal_3275_);
v___x_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
default: 
{
lean_object* v___x_3278_; 
lean_dec(v_x_3272_);
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_unsigned_to_nat(0u);
return v___x_3281_;
}
else
{
lean_object* v_val_3282_; 
v_val_3282_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v___x_3280_, 1);
return v_val_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Syntax_toNat(v_stx_3283_);
lean_dec(v_stx_3283_);
return v_res_3284_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = 9;
v___x_3286_ = lean_box_uint32(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = 10;
v___x_3288_ = lean_box_uint32(v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = 13;
v___x_3290_ = lean_box_uint32(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = 39;
v___x_3292_ = lean_box_uint32(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = 34;
v___x_3294_ = lean_box_uint32(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = 92;
v___x_3296_ = lean_box_uint32(v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3297_, lean_object* v_i_3298_){
_start:
{
uint32_t v_c_3299_; lean_object* v_i_3300_; uint32_t v___x_3301_; uint8_t v___x_3302_; 
v_c_3299_ = lean_string_utf8_get(v_s_3297_, v_i_3298_);
v_i_3300_ = lean_string_utf8_next(v_s_3297_, v_i_3298_);
v___x_3301_ = 92;
v___x_3302_ = lean_uint32_dec_eq(v_c_3299_, v___x_3301_);
if (v___x_3302_ == 0)
{
uint32_t v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = 34;
v___x_3304_ = lean_uint32_dec_eq(v_c_3299_, v___x_3303_);
if (v___x_3304_ == 0)
{
uint32_t v___x_3305_; uint8_t v___x_3306_; 
v___x_3305_ = 39;
v___x_3306_ = lean_uint32_dec_eq(v_c_3299_, v___x_3305_);
if (v___x_3306_ == 0)
{
uint32_t v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = 114;
v___x_3308_ = lean_uint32_dec_eq(v_c_3299_, v___x_3307_);
if (v___x_3308_ == 0)
{
uint32_t v___x_3309_; uint8_t v___x_3310_; 
v___x_3309_ = 110;
v___x_3310_ = lean_uint32_dec_eq(v_c_3299_, v___x_3309_);
if (v___x_3310_ == 0)
{
uint32_t v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = 116;
v___x_3312_ = lean_uint32_dec_eq(v_c_3299_, v___x_3311_);
if (v___x_3312_ == 0)
{
uint32_t v___x_3313_; uint8_t v___x_3314_; 
v___x_3313_ = 120;
v___x_3314_ = lean_uint32_dec_eq(v_c_3299_, v___x_3313_);
if (v___x_3314_ == 0)
{
uint32_t v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = 117;
v___x_3316_ = lean_uint32_dec_eq(v_c_3299_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; 
lean_dec(v_i_3300_);
v___x_3317_ = lean_box(0);
return v___x_3317_;
}
else
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3297_, v_i_3300_);
lean_dec(v_i_3300_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_box(0);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3323_; 
v_val_3320_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v___x_3318_, 1);
v_fst_3321_ = lean_ctor_get(v_val_3320_, 0);
lean_inc(v_fst_3321_);
v_snd_3322_ = lean_ctor_get(v_val_3320_, 1);
lean_inc(v_snd_3322_);
lean_dec(v_val_3320_);
v___x_3323_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3297_, v_snd_3322_);
lean_dec(v_snd_3322_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; 
lean_dec(v_fst_3321_);
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
v___x_3328_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3297_, v_snd_3327_);
lean_dec(v_snd_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
lean_dec(v_fst_3326_);
lean_dec(v_fst_3321_);
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
v___x_3333_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3297_, v_snd_3332_);
lean_dec(v_snd_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; 
lean_dec(v_fst_3331_);
lean_dec(v_fst_3326_);
lean_dec(v_fst_3321_);
v___x_3334_ = lean_box(0);
return v___x_3334_;
}
else
{
lean_object* v_val_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3360_; 
v_val_3335_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3337_ = v___x_3333_;
v_isShared_3338_ = v_isSharedCheck_3360_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_val_3335_);
lean_dec(v___x_3333_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3360_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_fst_3339_; lean_object* v_snd_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3359_; 
v_fst_3339_ = lean_ctor_get(v_val_3335_, 0);
v_snd_3340_ = lean_ctor_get(v_val_3335_, 1);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_val_3335_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3342_ = v_val_3335_;
v_isShared_3343_ = v_isSharedCheck_3359_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_snd_3340_);
lean_inc(v_fst_3339_);
lean_dec(v_val_3335_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3359_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint32_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3344_ = lean_unsigned_to_nat(16u);
v___x_3345_ = lean_nat_mul(v___x_3344_, v_fst_3321_);
lean_dec(v_fst_3321_);
v___x_3346_ = lean_nat_add(v___x_3345_, v_fst_3326_);
lean_dec(v_fst_3326_);
lean_dec(v___x_3345_);
v___x_3347_ = lean_nat_mul(v___x_3344_, v___x_3346_);
lean_dec(v___x_3346_);
v___x_3348_ = lean_nat_add(v___x_3347_, v_fst_3331_);
lean_dec(v_fst_3331_);
lean_dec(v___x_3347_);
v___x_3349_ = lean_nat_mul(v___x_3344_, v___x_3348_);
lean_dec(v___x_3348_);
v___x_3350_ = lean_nat_add(v___x_3349_, v_fst_3339_);
lean_dec(v_fst_3339_);
lean_dec(v___x_3349_);
v___x_3351_ = l_Char_ofNat(v___x_3350_);
lean_dec(v___x_3350_);
v___x_3352_ = lean_box_uint32(v___x_3351_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v___x_3352_);
v___x_3354_ = v___x_3342_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_snd_3340_);
v___x_3354_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3356_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3354_);
v___x_3356_ = v___x_3337_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
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
lean_object* v___x_3361_; 
v___x_3361_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3297_, v_i_3300_);
lean_dec(v_i_3300_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
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
v___x_3366_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3297_, v_snd_3365_);
lean_dec(v_snd_3365_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec(v_fst_3364_);
v___x_3367_ = lean_box(0);
return v___x_3367_;
}
else
{
lean_object* v_val_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3389_; 
v_val_3368_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3389_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_val_3368_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3389_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3388_; 
v_fst_3372_ = lean_ctor_get(v_val_3368_, 0);
v_snd_3373_ = lean_ctor_get(v_val_3368_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_val_3368_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3375_ = v_val_3368_;
v_isShared_3376_ = v_isSharedCheck_3388_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3372_);
lean_dec(v_val_3368_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3388_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint32_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3377_ = lean_unsigned_to_nat(16u);
v___x_3378_ = lean_nat_mul(v___x_3377_, v_fst_3364_);
lean_dec(v_fst_3364_);
v___x_3379_ = lean_nat_add(v___x_3378_, v_fst_3372_);
lean_dec(v_fst_3372_);
lean_dec(v___x_3378_);
v___x_3380_ = l_Char_ofNat(v___x_3379_);
lean_dec(v___x_3379_);
v___x_3381_ = lean_box_uint32(v___x_3380_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3381_);
v___x_3383_ = v___x_3375_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3373_);
v___x_3383_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3383_);
v___x_3385_ = v___x_3370_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
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
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v_i_3300_);
v___x_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v_i_3300_);
v___x_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v_i_3300_);
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
return v___x_3398_;
}
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3399_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v_i_3300_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v_i_3300_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v_i_3300_);
v___x_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3408_, lean_object* v_i_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Syntax_decodeQuotedChar(v_s_3408_, v_i_3409_);
lean_dec(v_i_3409_);
lean_dec_ref(v_s_3408_);
return v_res_3410_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3411_){
_start:
{
uint32_t v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = 32;
v___x_3413_ = lean_uint32_dec_eq(v___y_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
uint32_t v___x_3414_; uint8_t v___x_3415_; 
v___x_3414_ = 9;
v___x_3415_ = lean_uint32_dec_eq(v___y_3411_, v___x_3414_);
if (v___x_3415_ == 0)
{
uint32_t v___x_3416_; uint8_t v___x_3417_; 
v___x_3416_ = 13;
v___x_3417_ = lean_uint32_dec_eq(v___y_3411_, v___x_3416_);
if (v___x_3417_ == 0)
{
uint32_t v___x_3418_; uint8_t v___x_3419_; 
v___x_3418_ = 10;
v___x_3419_ = lean_uint32_dec_eq(v___y_3411_, v___x_3418_);
return v___x_3419_;
}
else
{
return v___x_3417_;
}
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
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3420_){
_start:
{
uint32_t v___y_264__boxed_3421_; uint8_t v_res_3422_; lean_object* v_r_3423_; 
v___y_264__boxed_3421_ = lean_unbox_uint32(v___y_3420_);
lean_dec(v___y_3420_);
v_res_3422_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_264__boxed_3421_);
v_r_3423_ = lean_box(v_res_3422_);
return v_r_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3425_, lean_object* v_i_3426_){
_start:
{
lean_object* v___f_3427_; uint32_t v___x_3432_; uint32_t v___x_3433_; uint8_t v___x_3434_; 
v___f_3427_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3432_ = lean_string_utf8_get(v_s_3425_, v_i_3426_);
v___x_3433_ = 32;
v___x_3434_ = lean_uint32_dec_eq(v___x_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
uint32_t v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = 9;
v___x_3436_ = lean_uint32_dec_eq(v___x_3432_, v___x_3435_);
if (v___x_3436_ == 0)
{
uint32_t v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = 13;
v___x_3438_ = lean_uint32_dec_eq(v___x_3432_, v___x_3437_);
if (v___x_3438_ == 0)
{
uint32_t v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = 10;
v___x_3440_ = lean_uint32_dec_eq(v___x_3432_, v___x_3439_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v_s_3425_);
v___x_3441_ = lean_box(0);
return v___x_3441_;
}
else
{
goto v___jp_3428_;
}
}
else
{
goto v___jp_3428_;
}
}
else
{
goto v___jp_3428_;
}
}
else
{
goto v___jp_3428_;
}
v___jp_3428_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_string_utf8_next(v_s_3425_, v_i_3426_);
v___x_3430_ = lean_string_nextwhile(v_s_3425_, v___f_3427_, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3442_, lean_object* v_i_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Syntax_decodeStringGap(v_s_3442_, v_i_3443_);
lean_dec(v_i_3443_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3445_, lean_object* v_i_3446_, lean_object* v_acc_3447_){
_start:
{
uint32_t v_c_3448_; uint32_t v___x_3449_; uint8_t v___x_3450_; 
v_c_3448_ = lean_string_utf8_get(v_s_3445_, v_i_3446_);
v___x_3449_ = 34;
v___x_3450_ = lean_uint32_dec_eq(v_c_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v_i_3451_; uint8_t v___x_3452_; 
v_i_3451_ = lean_string_utf8_next(v_s_3445_, v_i_3446_);
lean_dec(v_i_3446_);
v___x_3452_ = lean_string_utf8_at_end(v_s_3445_, v_i_3451_);
if (v___x_3452_ == 0)
{
uint32_t v___x_3453_; uint8_t v___x_3454_; 
v___x_3453_ = 92;
v___x_3454_ = lean_uint32_dec_eq(v_c_3448_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_string_push(v_acc_3447_, v_c_3448_);
v_i_3446_ = v_i_3451_;
v_acc_3447_ = v___x_3455_;
goto _start;
}
else
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_Syntax_decodeQuotedChar(v_s_3445_, v_i_3451_);
if (lean_obj_tag(v___x_3457_) == 1)
{
lean_object* v_val_3458_; lean_object* v_fst_3459_; lean_object* v_snd_3460_; uint32_t v___x_3461_; lean_object* v___x_3462_; 
lean_dec(v_i_3451_);
v_val_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_val_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v_fst_3459_ = lean_ctor_get(v_val_3458_, 0);
lean_inc(v_fst_3459_);
v_snd_3460_ = lean_ctor_get(v_val_3458_, 1);
lean_inc(v_snd_3460_);
lean_dec(v_val_3458_);
v___x_3461_ = lean_unbox_uint32(v_fst_3459_);
lean_dec(v_fst_3459_);
v___x_3462_ = lean_string_push(v_acc_3447_, v___x_3461_);
v_i_3446_ = v_snd_3460_;
v_acc_3447_ = v___x_3462_;
goto _start;
}
else
{
lean_object* v___x_3464_; 
lean_dec(v___x_3457_);
lean_inc_ref(v_s_3445_);
v___x_3464_ = l_Lean_Syntax_decodeStringGap(v_s_3445_, v_i_3451_);
lean_dec(v_i_3451_);
if (lean_obj_tag(v___x_3464_) == 1)
{
lean_object* v_val_3465_; 
v_val_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_val_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v_i_3446_ = v_val_3465_;
goto _start;
}
else
{
lean_object* v___x_3467_; 
lean_dec(v___x_3464_);
lean_dec_ref(v_acc_3447_);
lean_dec_ref(v_s_3445_);
v___x_3467_ = lean_box(0);
return v___x_3467_;
}
}
}
}
else
{
lean_object* v___x_3468_; 
lean_dec(v_i_3451_);
lean_dec_ref(v_acc_3447_);
lean_dec_ref(v_s_3445_);
v___x_3468_ = lean_box(0);
return v___x_3468_;
}
}
else
{
lean_object* v___x_3469_; 
lean_dec(v_i_3446_);
lean_dec_ref(v_s_3445_);
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v_acc_3447_);
return v___x_3469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3470_, lean_object* v_i_3471_, lean_object* v_num_3472_){
_start:
{
uint32_t v_c_3473_; lean_object* v_i_3474_; uint32_t v___x_3475_; uint8_t v___x_3476_; 
v_c_3473_ = lean_string_utf8_get(v_s_3470_, v_i_3471_);
v_i_3474_ = lean_string_utf8_next(v_s_3470_, v_i_3471_);
lean_dec(v_i_3471_);
v___x_3475_ = 35;
v___x_3476_ = lean_uint32_dec_eq(v_c_3473_, v___x_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3477_ = lean_string_utf8_byte_size(v_s_3470_);
v___x_3478_ = lean_unsigned_to_nat(1u);
v___x_3479_ = lean_nat_add(v_num_3472_, v___x_3478_);
lean_dec(v_num_3472_);
v___x_3480_ = lean_nat_sub(v___x_3477_, v___x_3479_);
lean_dec(v___x_3479_);
v___x_3481_ = lean_string_utf8_extract(v_s_3470_, v_i_3474_, v___x_3480_);
lean_dec(v___x_3480_);
lean_dec(v_i_3474_);
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = lean_unsigned_to_nat(1u);
v___x_3483_ = lean_nat_add(v_num_3472_, v___x_3482_);
lean_dec(v_num_3472_);
v_i_3471_ = v_i_3474_;
v_num_3472_ = v___x_3483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3485_, lean_object* v_i_3486_, lean_object* v_num_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3485_, v_i_3486_, v_num_3487_);
lean_dec_ref(v_s_3485_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3489_){
_start:
{
lean_object* v___x_3490_; uint32_t v___x_3491_; uint32_t v___x_3492_; uint8_t v___x_3493_; 
v___x_3490_ = lean_unsigned_to_nat(0u);
v___x_3491_ = lean_string_utf8_get(v_s_3489_, v___x_3490_);
v___x_3492_ = 114;
v___x_3493_ = lean_uint32_dec_eq(v___x_3491_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3495_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3496_ = l_Lean_Syntax_decodeStrLitAux(v_s_3489_, v___x_3494_, v___x_3495_);
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = lean_unsigned_to_nat(1u);
v___x_3498_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3489_, v___x_3497_, v___x_3490_);
lean_dec_ref(v_s_3489_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3500_){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3502_ = l_Lean_Syntax_isLit_x3f(v___x_3501_, v_stx_3500_);
if (lean_obj_tag(v___x_3502_) == 1)
{
lean_object* v_val_3503_; lean_object* v___x_3504_; 
v_val_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_val_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = l_Lean_Syntax_decodeStrLit(v_val_3503_);
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; 
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3506_);
lean_dec(v_stx_3506_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3508_){
_start:
{
lean_object* v___x_3509_; uint32_t v_c_3510_; uint32_t v___x_3511_; uint8_t v___x_3512_; 
v___x_3509_ = lean_unsigned_to_nat(1u);
v_c_3510_ = lean_string_utf8_get(v_s_3508_, v___x_3509_);
v___x_3511_ = 92;
v___x_3512_ = lean_uint32_dec_eq(v_c_3510_, v___x_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_box_uint32(v_c_3510_);
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_unsigned_to_nat(2u);
v___x_3516_ = l_Lean_Syntax_decodeQuotedChar(v_s_3508_, v___x_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_box(0);
return v___x_3517_;
}
else
{
lean_object* v_val_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3526_; 
v_val_3518_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3520_ = v___x_3516_;
v_isShared_3521_ = v_isSharedCheck_3526_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_val_3518_);
lean_dec(v___x_3516_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3526_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v_fst_3522_; lean_object* v___x_3524_; 
v_fst_3522_ = lean_ctor_get(v_val_3518_, 0);
lean_inc(v_fst_3522_);
lean_dec(v_val_3518_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v_fst_3522_);
v___x_3524_ = v___x_3520_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_fst_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Syntax_decodeCharLit(v_s_3527_);
lean_dec_ref(v_s_3527_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3529_){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3531_ = l_Lean_Syntax_isLit_x3f(v___x_3530_, v_stx_3529_);
if (lean_obj_tag(v___x_3531_) == 1)
{
lean_object* v_val_3532_; lean_object* v___x_3533_; 
v_val_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_val_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = l_Lean_Syntax_decodeCharLit(v_val_3532_);
lean_dec(v_val_3532_);
return v___x_3533_;
}
else
{
lean_object* v___x_3534_; 
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
return v___x_3534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3535_);
lean_dec(v_stx_3535_);
return v_res_3536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3537_){
_start:
{
uint8_t v___y_3555_; uint32_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = 65;
v___x_3561_ = lean_uint32_dec_le(v___x_3560_, v___y_3537_);
if (v___x_3561_ == 0)
{
v___y_3555_ = v___x_3561_;
goto v___jp_3554_;
}
else
{
uint32_t v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = 90;
v___x_3563_ = lean_uint32_dec_le(v___y_3537_, v___x_3562_);
v___y_3555_ = v___x_3563_;
goto v___jp_3554_;
}
v___jp_3538_:
{
uint32_t v___x_3539_; uint8_t v___x_3540_; 
v___x_3539_ = 95;
v___x_3540_ = lean_uint32_dec_eq(v___y_3537_, v___x_3539_);
if (v___x_3540_ == 0)
{
uint32_t v___x_3541_; uint8_t v___x_3542_; 
v___x_3541_ = 39;
v___x_3542_ = lean_uint32_dec_eq(v___y_3537_, v___x_3541_);
if (v___x_3542_ == 0)
{
uint32_t v___x_3543_; uint8_t v___x_3544_; 
v___x_3543_ = 33;
v___x_3544_ = lean_uint32_dec_eq(v___y_3537_, v___x_3543_);
if (v___x_3544_ == 0)
{
uint32_t v___x_3545_; uint8_t v___x_3546_; 
v___x_3545_ = 63;
v___x_3546_ = lean_uint32_dec_eq(v___y_3537_, v___x_3545_);
if (v___x_3546_ == 0)
{
uint8_t v___x_3547_; 
v___x_3547_ = l_Lean_isLetterLike(v___y_3537_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_isSubScriptAlnum(v___y_3537_);
return v___x_3548_;
}
else
{
return v___x_3547_;
}
}
else
{
return v___x_3546_;
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
v___jp_3549_:
{
uint32_t v___x_3550_; uint8_t v___x_3551_; 
v___x_3550_ = 48;
v___x_3551_ = lean_uint32_dec_le(v___x_3550_, v___y_3537_);
if (v___x_3551_ == 0)
{
goto v___jp_3538_;
}
else
{
uint32_t v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = 57;
v___x_3553_ = lean_uint32_dec_le(v___y_3537_, v___x_3552_);
if (v___x_3553_ == 0)
{
goto v___jp_3538_;
}
else
{
return v___x_3553_;
}
}
}
v___jp_3554_:
{
if (v___y_3555_ == 0)
{
uint32_t v___x_3556_; uint8_t v___x_3557_; 
v___x_3556_ = 97;
v___x_3557_ = lean_uint32_dec_le(v___x_3556_, v___y_3537_);
if (v___x_3557_ == 0)
{
goto v___jp_3549_;
}
else
{
uint32_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = 122;
v___x_3559_ = lean_uint32_dec_le(v___y_3537_, v___x_3558_);
if (v___x_3559_ == 0)
{
goto v___jp_3549_;
}
else
{
return v___x_3559_;
}
}
}
else
{
return v___y_3555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3564_){
_start:
{
uint32_t v___y_509__boxed_3565_; uint8_t v_res_3566_; lean_object* v_r_3567_; 
v___y_509__boxed_3565_ = lean_unbox_uint32(v___y_3564_);
lean_dec(v___y_3564_);
v_res_3566_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_509__boxed_3565_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3568_, uint32_t v___x_3569_, uint32_t v___y_3570_){
_start:
{
uint8_t v___x_3571_; 
v___x_3571_ = lean_uint32_dec_le(v___x_3568_, v___y_3570_);
if (v___x_3571_ == 0)
{
return v___x_3571_;
}
else
{
uint8_t v___x_3572_; 
v___x_3572_ = lean_uint32_dec_le(v___y_3570_, v___x_3569_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v___y_3575_){
_start:
{
uint32_t v___x_564__boxed_3576_; uint32_t v___x_565__boxed_3577_; uint32_t v___y_566__boxed_3578_; uint8_t v_res_3579_; lean_object* v_r_3580_; 
v___x_564__boxed_3576_ = lean_unbox_uint32(v___x_3573_);
lean_dec(v___x_3573_);
v___x_565__boxed_3577_ = lean_unbox_uint32(v___x_3574_);
lean_dec(v___x_3574_);
v___y_566__boxed_3578_ = lean_unbox_uint32(v___y_3575_);
lean_dec(v___y_3575_);
v_res_3579_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_564__boxed_3576_, v___x_565__boxed_3577_, v___y_566__boxed_3578_);
v_r_3580_ = lean_box(v_res_3579_);
return v_r_3580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3581_, uint8_t v___x_3582_, uint32_t v_x_3583_){
_start:
{
uint32_t v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = 187;
v___x_3585_ = lean_uint32_dec_eq(v_x_3583_, v___x_3584_);
if (v___x_3585_ == 0)
{
return v___x_3581_;
}
else
{
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3586_, lean_object* v___x_3587_, lean_object* v_x_3588_){
_start:
{
uint8_t v___x_577__boxed_3589_; uint8_t v___x_578__boxed_3590_; uint32_t v_x_579__boxed_3591_; uint8_t v_res_3592_; lean_object* v_r_3593_; 
v___x_577__boxed_3589_ = lean_unbox(v___x_3586_);
v___x_578__boxed_3590_ = lean_unbox(v___x_3587_);
v_x_579__boxed_3591_ = lean_unbox_uint32(v_x_3588_);
lean_dec(v_x_3588_);
v_res_3592_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_577__boxed_3589_, v___x_578__boxed_3590_, v_x_579__boxed_3591_);
v_r_3593_ = lean_box(v_res_3592_);
return v_r_3593_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = 48;
v___x_3596_ = lean_box_uint32(v___x_3595_);
return v___x_3596_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = 57;
v___x_3598_ = lean_box_uint32(v___x_3597_);
return v___x_3598_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___f_3601_; 
v___x_3599_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3600_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3601_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3601_, 0, v___x_3599_);
lean_closure_set(v___f_3601_, 1, v___x_3600_);
return v___f_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3602_, lean_object* v_acc_3603_){
_start:
{
lean_object* v_ss_3605_; lean_object* v_acc_3606_; uint8_t v___x_3615_; 
lean_inc_ref(v_ss_3602_);
v___x_3615_ = lean_substring_isempty(v_ss_3602_);
if (v___x_3615_ == 0)
{
uint32_t v_curr_3616_; uint32_t v___x_3617_; uint8_t v___x_3618_; 
lean_inc_ref(v_ss_3602_);
v_curr_3616_ = lean_substring_front(v_ss_3602_);
v___x_3617_ = 171;
v___x_3618_ = lean_uint32_dec_eq(v_curr_3616_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___f_3619_; uint8_t v___y_3651_; uint32_t v___x_3656_; uint8_t v___x_3657_; 
v___f_3619_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3656_ = 65;
v___x_3657_ = lean_uint32_dec_le(v___x_3656_, v_curr_3616_);
if (v___x_3657_ == 0)
{
v___y_3651_ = v___x_3657_;
goto v___jp_3650_;
}
else
{
uint32_t v___x_3658_; uint8_t v___x_3659_; 
v___x_3658_ = 90;
v___x_3659_ = lean_uint32_dec_le(v_curr_3616_, v___x_3658_);
v___y_3651_ = v___x_3659_;
goto v___jp_3650_;
}
v___jp_3620_:
{
lean_object* v_idPart_3621_; lean_object* v_startPos_3622_; lean_object* v_stopPos_3623_; lean_object* v_startPos_3624_; lean_object* v_stopPos_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_inc_ref(v_ss_3602_);
v_idPart_3621_ = lean_substring_takewhile(v_ss_3602_, v___f_3619_);
v_startPos_3622_ = lean_ctor_get(v_idPart_3621_, 1);
lean_inc(v_startPos_3622_);
v_stopPos_3623_ = lean_ctor_get(v_idPart_3621_, 2);
lean_inc(v_stopPos_3623_);
v_startPos_3624_ = lean_ctor_get(v_ss_3602_, 1);
v_stopPos_3625_ = lean_ctor_get(v_ss_3602_, 2);
v___x_3626_ = lean_nat_sub(v_stopPos_3623_, v_startPos_3622_);
lean_dec(v_startPos_3622_);
lean_dec(v_stopPos_3623_);
v___x_3627_ = lean_nat_sub(v_stopPos_3625_, v_startPos_3624_);
v___x_3628_ = lean_substring_extract(v_ss_3602_, v___x_3626_, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3629_, 0, v_idPart_3621_);
lean_ctor_set(v___x_3629_, 1, v_acc_3603_);
v_ss_3605_ = v___x_3628_;
v_acc_3606_ = v___x_3629_;
goto v___jp_3604_;
}
v___jp_3630_:
{
uint32_t v___x_3631_; uint8_t v___x_3632_; 
v___x_3631_ = 95;
v___x_3632_ = lean_uint32_dec_eq(v_curr_3616_, v___x_3631_);
if (v___x_3632_ == 0)
{
uint8_t v___x_3633_; 
v___x_3633_ = l_Lean_isLetterLike(v_curr_3616_);
if (v___x_3633_ == 0)
{
uint32_t v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = 48;
v___x_3635_ = lean_uint32_dec_le(v___x_3634_, v_curr_3616_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
lean_dec(v_acc_3603_);
lean_dec_ref(v_ss_3602_);
v___x_3636_ = lean_box(0);
return v___x_3636_;
}
else
{
uint32_t v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = 57;
v___x_3638_ = lean_uint32_dec_le(v_curr_3616_, v___x_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; 
lean_dec(v_acc_3603_);
lean_dec_ref(v_ss_3602_);
v___x_3639_ = lean_box(0);
return v___x_3639_;
}
else
{
lean_object* v___f_3640_; lean_object* v_idPart_3641_; lean_object* v_startPos_3642_; lean_object* v_stopPos_3643_; lean_object* v_startPos_3644_; lean_object* v_stopPos_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___f_3640_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3602_);
v_idPart_3641_ = lean_substring_takewhile(v_ss_3602_, v___f_3640_);
v_startPos_3642_ = lean_ctor_get(v_idPart_3641_, 1);
lean_inc(v_startPos_3642_);
v_stopPos_3643_ = lean_ctor_get(v_idPart_3641_, 2);
lean_inc(v_stopPos_3643_);
v_startPos_3644_ = lean_ctor_get(v_ss_3602_, 1);
v_stopPos_3645_ = lean_ctor_get(v_ss_3602_, 2);
v___x_3646_ = lean_nat_sub(v_stopPos_3643_, v_startPos_3642_);
lean_dec(v_startPos_3642_);
lean_dec(v_stopPos_3643_);
v___x_3647_ = lean_nat_sub(v_stopPos_3645_, v_startPos_3644_);
v___x_3648_ = lean_substring_extract(v_ss_3602_, v___x_3646_, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3649_, 0, v_idPart_3641_);
lean_ctor_set(v___x_3649_, 1, v_acc_3603_);
v_ss_3605_ = v___x_3648_;
v_acc_3606_ = v___x_3649_;
goto v___jp_3604_;
}
}
}
else
{
goto v___jp_3620_;
}
}
else
{
goto v___jp_3620_;
}
}
v___jp_3650_:
{
if (v___y_3651_ == 0)
{
uint32_t v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = 97;
v___x_3653_ = lean_uint32_dec_le(v___x_3652_, v_curr_3616_);
if (v___x_3653_ == 0)
{
goto v___jp_3630_;
}
else
{
uint32_t v___x_3654_; uint8_t v___x_3655_; 
v___x_3654_ = 122;
v___x_3655_ = lean_uint32_dec_le(v_curr_3616_, v___x_3654_);
if (v___x_3655_ == 0)
{
goto v___jp_3630_;
}
else
{
goto v___jp_3620_;
}
}
}
else
{
goto v___jp_3620_;
}
}
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v_escapedPart_3663_; lean_object* v_str_3664_; lean_object* v_startPos_3665_; lean_object* v_stopPos_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3687_; 
v___x_3660_ = lean_box(v___x_3618_);
v___x_3661_ = lean_box(v___x_3615_);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3662_, 0, v___x_3660_);
lean_closure_set(v___f_3662_, 1, v___x_3661_);
lean_inc_ref(v_ss_3602_);
v_escapedPart_3663_ = lean_substring_takewhile(v_ss_3602_, v___f_3662_);
v_str_3664_ = lean_ctor_get(v_escapedPart_3663_, 0);
v_startPos_3665_ = lean_ctor_get(v_escapedPart_3663_, 1);
v_stopPos_3666_ = lean_ctor_get(v_escapedPart_3663_, 2);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_escapedPart_3663_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3668_ = v_escapedPart_3663_;
v_isShared_3669_ = v_isSharedCheck_3687_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_stopPos_3666_);
lean_inc(v_startPos_3665_);
lean_inc(v_str_3664_);
lean_dec(v_escapedPart_3663_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3687_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v_startPos_3670_; lean_object* v_stopPos_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v_escapedPart_3675_; 
v_startPos_3670_ = lean_ctor_get(v_ss_3602_, 1);
v_stopPos_3671_ = lean_ctor_get(v_ss_3602_, 2);
v___x_3672_ = lean_string_utf8_next(v_str_3664_, v_stopPos_3666_);
lean_dec(v_stopPos_3666_);
lean_inc(v_stopPos_3671_);
v___x_3673_ = lean_string_pos_min(v_stopPos_3671_, v___x_3672_);
lean_inc(v___x_3673_);
lean_inc(v_startPos_3665_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 2, v___x_3673_);
v_escapedPart_3675_ = v___x_3668_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_str_3664_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_startPos_3665_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v___x_3673_);
v_escapedPart_3675_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; uint32_t v___x_3678_; uint32_t v___x_3679_; uint8_t v___x_3680_; 
v___x_3676_ = lean_nat_sub(v___x_3673_, v_startPos_3665_);
lean_dec(v_startPos_3665_);
lean_dec(v___x_3673_);
lean_inc(v___x_3676_);
lean_inc_ref_n(v_escapedPart_3675_, 2);
v___x_3677_ = lean_substring_prev(v_escapedPart_3675_, v___x_3676_);
v___x_3678_ = lean_substring_get(v_escapedPart_3675_, v___x_3677_);
v___x_3679_ = 187;
v___x_3680_ = lean_uint32_dec_eq(v___x_3678_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; 
lean_dec(v___x_3676_);
lean_dec_ref(v_escapedPart_3675_);
lean_dec(v_acc_3603_);
lean_dec_ref(v_ss_3602_);
v___x_3681_ = lean_box(0);
return v___x_3681_;
}
else
{
if (v___x_3615_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = lean_nat_sub(v_stopPos_3671_, v_startPos_3670_);
v___x_3683_ = lean_substring_extract(v_ss_3602_, v___x_3676_, v___x_3682_);
v___x_3684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3684_, 0, v_escapedPart_3675_);
lean_ctor_set(v___x_3684_, 1, v_acc_3603_);
v_ss_3605_ = v___x_3683_;
v_acc_3606_ = v___x_3684_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3685_; 
lean_dec(v___x_3676_);
lean_dec_ref(v_escapedPart_3675_);
lean_dec(v_acc_3603_);
lean_dec_ref(v_ss_3602_);
v___x_3685_ = lean_box(0);
return v___x_3685_;
}
}
}
}
}
}
else
{
lean_object* v___x_3688_; 
lean_dec(v_acc_3603_);
lean_dec_ref(v_ss_3602_);
v___x_3688_ = lean_box(0);
return v___x_3688_;
}
v___jp_3604_:
{
uint32_t v___x_3607_; uint32_t v___x_3608_; uint8_t v___x_3609_; 
lean_inc_ref(v_ss_3605_);
v___x_3607_ = lean_substring_front(v_ss_3605_);
v___x_3608_ = 46;
v___x_3609_ = lean_uint32_dec_eq(v___x_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_substring_isempty(v_ss_3605_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec(v_acc_3606_);
v___x_3611_ = lean_box(0);
return v___x_3611_;
}
else
{
return v_acc_3606_;
}
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_unsigned_to_nat(1u);
v___x_3613_ = lean_substring_drop(v_ss_3605_, v___x_3612_);
v_ss_3602_ = v___x_3613_;
v_acc_3603_ = v_acc_3606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3689_){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_box(0);
v___x_3691_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3689_, v___x_3690_);
v___x_3692_ = l_List_reverse___redArg(v___x_3691_);
return v___x_3692_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3696_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3697_ = lean_unsigned_to_nat(10u);
v___x_3698_ = lean_unsigned_to_nat(1240u);
v___x_3699_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3700_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3701_ = l_mkPanicMessageWithDecl(v___x_3700_, v___x_3699_, v___x_3698_, v___x_3697_, v___x_3696_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3702_, lean_object* v_x_3703_){
_start:
{
if (lean_obj_tag(v_x_3703_) == 0)
{
lean_inc(v_init_3702_);
return v_init_3702_;
}
else
{
lean_object* v_head_3704_; lean_object* v_tail_3705_; lean_object* v___x_3706_; lean_object* v_comp_3707_; uint32_t v___x_3708_; uint32_t v___x_3709_; uint8_t v___x_3710_; 
v_head_3704_ = lean_ctor_get(v_x_3703_, 0);
lean_inc(v_head_3704_);
v_tail_3705_ = lean_ctor_get(v_x_3703_, 1);
lean_inc(v_tail_3705_);
lean_dec_ref_known(v_x_3703_, 2);
v___x_3706_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3702_, v_tail_3705_);
v_comp_3707_ = lean_substring_tostring(v_head_3704_);
lean_inc_ref(v_comp_3707_);
v___x_3708_ = lean_string_front(v_comp_3707_);
v___x_3709_ = 171;
v___x_3710_ = lean_uint32_dec_eq(v___x_3708_, v___x_3709_);
if (v___x_3710_ == 0)
{
uint32_t v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = 48;
v___x_3712_ = lean_uint32_dec_le(v___x_3711_, v___x_3708_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Name_str___override(v___x_3706_, v_comp_3707_);
return v___x_3713_;
}
else
{
uint32_t v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = 57;
v___x_3715_ = lean_uint32_dec_le(v___x_3708_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Name_str___override(v___x_3706_, v_comp_3707_);
return v___x_3716_;
}
else
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3707_);
lean_dec_ref(v_comp_3707_);
if (lean_obj_tag(v___x_3717_) == 1)
{
lean_object* v_val_3718_; lean_object* v___x_3719_; 
v_val_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_val_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = l_Lean_Name_num___override(v___x_3706_, v_val_3718_);
return v___x_3719_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
lean_dec(v___x_3717_);
lean_dec(v___x_3706_);
v___x_3720_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3721_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3720_);
return v___x_3721_;
}
}
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3722_ = lean_unsigned_to_nat(1u);
v___x_3723_ = lean_string_drop(v_comp_3707_, v___x_3722_);
v___x_3724_ = lean_string_dropright(v___x_3723_, v___x_3722_);
v___x_3725_ = l_Lean_Name_str___override(v___x_3706_, v___x_3724_);
return v___x_3725_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3726_, lean_object* v_x_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3726_, v_x_3727_);
lean_dec(v_init_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3729_){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_box(0);
v___x_3731_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3729_, v___x_3730_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_box(0);
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = lean_box(0);
v___x_3734_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3733_, v___x_3731_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3736_ = lean_unsigned_to_nat(0u);
v___x_3737_ = lean_string_utf8_byte_size(v_s_3735_);
v___x_3738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3738_, 0, v_s_3735_);
lean_ctor_set(v___x_3738_, 1, v___x_3736_);
lean_ctor_set(v___x_3738_, 2, v___x_3737_);
v___x_3739_ = l_Substring_Raw_toName(v___x_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3740_){
_start:
{
lean_object* v___x_3741_; uint32_t v___x_3742_; uint32_t v___x_3743_; uint8_t v___x_3744_; 
v___x_3741_ = lean_unsigned_to_nat(0u);
v___x_3742_ = lean_string_utf8_get(v_s_3740_, v___x_3741_);
v___x_3743_ = 96;
v___x_3744_ = lean_uint32_dec_eq(v___x_3742_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; 
lean_dec_ref(v_s_3740_);
v___x_3745_ = lean_box(0);
return v___x_3745_;
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3746_ = lean_string_utf8_byte_size(v_s_3740_);
v___x_3747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3747_, 0, v_s_3740_);
lean_ctor_set(v___x_3747_, 1, v___x_3741_);
lean_ctor_set(v___x_3747_, 2, v___x_3746_);
v___x_3748_ = lean_unsigned_to_nat(1u);
v___x_3749_ = lean_substring_drop(v___x_3747_, v___x_3748_);
v___x_3750_ = l_Substring_Raw_toName(v___x_3749_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_box(0);
return v___x_3751_;
}
else
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
return v___x_3752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3753_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3755_ = l_Lean_Syntax_isLit_x3f(v___x_3754_, v_stx_3753_);
if (lean_obj_tag(v___x_3755_) == 1)
{
lean_object* v_val_3756_; lean_object* v___x_3757_; 
v_val_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_val_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = l_Lean_Syntax_decodeNameLit(v_val_3756_);
return v___x_3757_;
}
else
{
lean_object* v___x_3758_; 
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
return v___x_3758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3759_);
lean_dec(v_stx_3759_);
return v_res_3760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3761_){
_start:
{
if (lean_obj_tag(v_x_3761_) == 1)
{
lean_object* v_args_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v_args_3762_ = lean_ctor_get(v_x_3761_, 2);
v___x_3763_ = lean_unsigned_to_nat(0u);
v___x_3764_ = lean_array_get_size(v_args_3762_);
v___x_3765_ = lean_nat_dec_lt(v___x_3763_, v___x_3764_);
return v___x_3765_;
}
else
{
uint8_t v___x_3766_; 
v___x_3766_ = 0;
return v___x_3766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3767_){
_start:
{
uint8_t v_res_3768_; lean_object* v_r_3769_; 
v_res_3768_ = l_Lean_Syntax_hasArgs(v_x_3767_);
lean_dec(v_x_3767_);
v_r_3769_ = lean_box(v_res_3768_);
return v_r_3769_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3770_){
_start:
{
if (lean_obj_tag(v_x_3770_) == 2)
{
uint8_t v___x_3771_; 
v___x_3771_ = 1;
return v___x_3771_;
}
else
{
uint8_t v___x_3772_; 
v___x_3772_ = 0;
return v___x_3772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3773_){
_start:
{
uint8_t v_res_3774_; lean_object* v_r_3775_; 
v_res_3774_ = l_Lean_Syntax_isAtom(v_x_3773_);
lean_dec(v_x_3773_);
v_r_3775_ = lean_box(v_res_3774_);
return v_r_3775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3776_, lean_object* v_x_3777_){
_start:
{
if (lean_obj_tag(v_x_3777_) == 2)
{
lean_object* v_val_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v_val_3778_ = lean_ctor_get(v_x_3777_, 1);
lean_inc_ref(v_val_3778_);
lean_dec_ref_known(v_x_3777_, 2);
v___x_3779_ = lean_string_trim(v_val_3778_);
v___x_3780_ = lean_string_trim(v_token_3776_);
v___x_3781_ = lean_string_dec_eq(v___x_3779_, v___x_3780_);
lean_dec_ref(v___x_3780_);
lean_dec_ref(v___x_3779_);
return v___x_3781_;
}
else
{
uint8_t v___x_3782_; 
lean_dec(v_x_3777_);
lean_dec_ref(v_token_3776_);
v___x_3782_ = 0;
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3783_, lean_object* v_x_3784_){
_start:
{
uint8_t v_res_3785_; lean_object* v_r_3786_; 
v_res_3785_ = l_Lean_Syntax_isToken(v_token_3783_, v_x_3784_);
v_r_3786_ = lean_box(v_res_3785_);
return v_r_3786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3787_){
_start:
{
switch(lean_obj_tag(v_stx_3787_))
{
case 1:
{
lean_object* v_kind_3788_; lean_object* v_args_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; 
v_kind_3788_ = lean_ctor_get(v_stx_3787_, 1);
v_args_3789_ = lean_ctor_get(v_stx_3787_, 2);
v___x_3790_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3791_ = lean_name_eq(v_kind_3788_, v___x_3790_);
if (v___x_3791_ == 0)
{
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3792_ = lean_array_get_size(v_args_3789_);
v___x_3793_ = lean_unsigned_to_nat(0u);
v___x_3794_ = lean_nat_dec_eq(v___x_3792_, v___x_3793_);
return v___x_3794_;
}
}
case 0:
{
uint8_t v___x_3795_; 
v___x_3795_ = 1;
return v___x_3795_;
}
default: 
{
uint8_t v___x_3796_; 
v___x_3796_ = 0;
return v___x_3796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3797_){
_start:
{
uint8_t v_res_3798_; lean_object* v_r_3799_; 
v_res_3798_ = l_Lean_Syntax_isNone(v_stx_3797_);
lean_dec(v_stx_3797_);
v_r_3799_ = lean_box(v_res_3798_);
return v_r_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3800_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_Syntax_getOptional_x3f(v_stx_3800_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_box(0);
return v___x_3802_;
}
else
{
lean_object* v_val_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3811_; 
v_val_3803_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3805_ = v___x_3801_;
v_isShared_3806_ = v_isSharedCheck_3811_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_val_3803_);
lean_dec(v___x_3801_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3811_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = l_Lean_Syntax_getId(v_val_3803_);
lean_dec(v_val_3803_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3812_);
lean_dec(v_stx_3812_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3814_, lean_object* v_x_3815_){
_start:
{
if (lean_obj_tag(v_x_3815_) == 1)
{
lean_object* v_args_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v_args_3816_ = lean_ctor_get(v_x_3815_, 2);
lean_inc_ref(v_p_3814_);
lean_inc_ref(v_x_3815_);
v___x_3817_ = lean_apply_1(v_p_3814_, v_x_3815_);
v___x_3818_ = lean_unbox(v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; lean_object* v___x_3820_; size_t v_sz_3821_; size_t v___x_3822_; lean_object* v___x_3823_; lean_object* v_fst_3824_; 
lean_inc_ref(v_args_3816_);
lean_dec_ref_known(v_x_3815_, 3);
v___x_3819_ = lean_box(0);
v___x_3820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3821_ = lean_array_size(v_args_3816_);
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3814_, v_args_3816_, v_sz_3821_, v___x_3822_, v___x_3820_);
lean_dec_ref(v_args_3816_);
v_fst_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_fst_3824_);
lean_dec_ref(v___x_3823_);
if (lean_obj_tag(v_fst_3824_) == 0)
{
return v___x_3819_;
}
else
{
lean_object* v_val_3825_; 
v_val_3825_ = lean_ctor_get(v_fst_3824_, 0);
lean_inc(v_val_3825_);
lean_dec_ref_known(v_fst_3824_, 1);
return v_val_3825_;
}
}
else
{
lean_object* v___x_3826_; 
lean_dec_ref(v_p_3814_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_x_3815_);
return v___x_3826_;
}
}
else
{
lean_object* v___x_3827_; uint8_t v___x_3828_; 
lean_inc(v_x_3815_);
v___x_3827_ = lean_apply_1(v_p_3814_, v_x_3815_);
v___x_3828_ = lean_unbox(v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_dec(v_x_3815_);
v___x_3829_ = lean_box(0);
return v___x_3829_;
}
else
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_x_3815_);
return v___x_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3831_, lean_object* v_as_3832_, size_t v_sz_3833_, size_t v_i_3834_, lean_object* v_b_3835_){
_start:
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_usize_dec_lt(v_i_3834_, v_sz_3833_);
if (v___x_3836_ == 0)
{
lean_dec_ref(v_p_3831_);
lean_inc_ref(v_b_3835_);
return v_b_3835_;
}
else
{
lean_object* v___x_3837_; lean_object* v_a_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_box(0);
v_a_3838_ = lean_array_uget_borrowed(v_as_3832_, v_i_3834_);
lean_inc(v_a_3838_);
lean_inc_ref(v_p_3831_);
v___x_3839_ = l_Lean_Syntax_findAux(v_p_3831_, v_a_3838_);
if (lean_obj_tag(v___x_3839_) == 1)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec_ref(v_p_3831_);
v___x_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
lean_ctor_set(v___x_3841_, 1, v___x_3837_);
return v___x_3841_;
}
else
{
lean_object* v___x_3842_; size_t v___x_3843_; size_t v___x_3844_; 
lean_dec(v___x_3839_);
v___x_3842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3834_, v___x_3843_);
v_i_3834_ = v___x_3844_;
v_b_3835_ = v___x_3842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3846_, lean_object* v_as_3847_, lean_object* v_sz_3848_, lean_object* v_i_3849_, lean_object* v_b_3850_){
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3848_);
lean_dec(v_sz_3848_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3849_);
lean_dec(v_i_3849_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3846_, v_as_3847_, v_sz_boxed_3851_, v_i_boxed_3852_, v_b_3850_);
lean_dec_ref(v_b_3850_);
lean_dec_ref(v_as_3847_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3854_, lean_object* v_p_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Lean_Syntax_findAux(v_p_3855_, v_stx_3854_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Syntax_isNatLit_x3f(v_s_3857_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_unsigned_to_nat(0u);
return v___x_3859_;
}
else
{
lean_object* v_val_3860_; 
v_val_3860_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v___x_3858_, 1);
return v_val_3860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_TSyntax_getNat(v_s_3861_);
lean_dec(v_s_3861_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3866_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3868_ = l_Lean_Syntax_isLit_x3f(v___x_3867_, v_stx_3866_);
if (lean_obj_tag(v___x_3868_) == 1)
{
lean_object* v_val_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_val_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_val_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3870_ = lean_unsigned_to_nat(0u);
v___x_3871_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3869_, v___x_3870_, v___x_3870_);
lean_dec(v_val_3869_);
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; 
lean_dec(v___x_3868_);
v___x_3872_ = lean_box(0);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3873_);
lean_dec(v_stx_3873_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3875_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
return v___x_3877_;
}
else
{
lean_object* v_val_3878_; 
v_val_3878_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_val_3878_);
lean_dec_ref_known(v___x_3876_, 1);
return v_val_3878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_TSyntax_getHexNumVal(v_s_3879_);
lean_dec(v_s_3879_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3881_, lean_object* v_p_3882_, lean_object* v_n_3883_){
_start:
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_string_utf8_at_end(v_s_3881_, v_p_3882_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; uint32_t v___x_3886_; uint32_t v___x_3887_; uint8_t v___x_3888_; 
v___x_3885_ = lean_string_utf8_next(v_s_3881_, v_p_3882_);
v___x_3886_ = lean_string_utf8_get(v_s_3881_, v_p_3882_);
lean_dec(v_p_3882_);
v___x_3887_ = 95;
v___x_3888_ = lean_uint32_dec_eq(v___x_3886_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_unsigned_to_nat(1u);
v___x_3890_ = lean_nat_add(v_n_3883_, v___x_3889_);
lean_dec(v_n_3883_);
v_p_3882_ = v___x_3885_;
v_n_3883_ = v___x_3890_;
goto _start;
}
else
{
v_p_3882_ = v___x_3885_;
goto _start;
}
}
else
{
lean_dec(v_p_3882_);
return v_n_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3893_, lean_object* v_p_3894_, lean_object* v_n_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3893_, v_p_3894_, v_n_3895_);
lean_dec_ref(v_s_3893_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3897_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3899_ = l_Lean_Syntax_isLit_x3f(v___x_3898_, v_s_3897_);
if (lean_obj_tag(v___x_3899_) == 1)
{
lean_object* v_val_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_val_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_val_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = lean_unsigned_to_nat(0u);
v___x_3902_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3900_, v___x_3901_, v___x_3901_);
lean_dec(v_val_3900_);
return v___x_3902_;
}
else
{
lean_object* v___x_3903_; 
lean_dec(v___x_3899_);
v___x_3903_ = lean_unsigned_to_nat(0u);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_TSyntax_getHexNumSize(v_s_3904_);
lean_dec(v_s_3904_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_Syntax_getId(v_s_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l_Lean_TSyntax_getId(v_s_3908_);
lean_dec(v_s_3908_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3917_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3919_; 
v___x_3919_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3919_;
}
else
{
lean_object* v_val_3920_; 
v_val_3920_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_val_3920_);
lean_dec_ref_known(v___x_3918_, 1);
return v_val_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_TSyntax_getScientific(v_s_3921_);
lean_dec(v_s_3921_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3923_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Lean_Syntax_isStrLit_x3f(v_s_3923_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v___x_3925_; 
v___x_3925_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3925_;
}
else
{
lean_object* v_val_3926_; 
v_val_3926_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_val_3926_);
lean_dec_ref_known(v___x_3924_, 1);
return v_val_3926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_TSyntax_getString(v_s_3927_);
lean_dec(v_s_3927_);
return v_res_3928_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Syntax_isCharLit_x3f(v_s_3929_);
if (lean_obj_tag(v___x_3930_) == 0)
{
uint32_t v___x_3931_; 
v___x_3931_ = 65;
return v___x_3931_;
}
else
{
lean_object* v_val_3932_; uint32_t v___x_3933_; 
v_val_3932_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_val_3932_);
lean_dec_ref_known(v___x_3930_, 1);
v___x_3933_ = lean_unbox_uint32(v_val_3932_);
lean_dec(v_val_3932_);
return v___x_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3934_){
_start:
{
uint32_t v_res_3935_; lean_object* v_r_3936_; 
v_res_3935_ = l_Lean_TSyntax_getChar(v_s_3934_);
lean_dec(v_s_3934_);
v_r_3936_ = lean_box_uint32(v_res_3935_);
return v_r_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_Syntax_isNameLit_x3f(v_s_3937_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_TSyntax_getName(v_s_3941_);
lean_dec(v_s_3941_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3943_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_unsigned_to_nat(0u);
v___x_3945_ = l_Lean_Syntax_getArg(v_s_3943_, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_getId(v___x_3945_);
lean_dec(v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_TSyntax_getHygieneInfo(v_s_3947_);
lean_dec(v_s_3947_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3949_, v_a_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3952_, v_a_3953_);
lean_dec_ref(v_a_3953_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3955_){
_start:
{
lean_object* v___f_3956_; 
v___f_3956_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3956_, 0, v_sep_3955_);
return v___f_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3957_, lean_object* v_sep_3958_){
_start:
{
lean_object* v___f_3959_; 
v___f_3959_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3959_, 0, v_sep_3958_);
return v___f_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3960_, lean_object* v_sep_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3960_, v_sep_3961_);
lean_dec(v_k_3960_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3963_, lean_object* v_val_3964_, uint8_t v_canonical_3965_){
_start:
{
lean_object* v___x_3966_; lean_object* v_src_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v_imported_3970_; lean_object* v_ctx_3971_; lean_object* v_scopes_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3988_; 
v___x_3966_ = lean_unsigned_to_nat(0u);
v_src_3967_ = l_Lean_Syntax_getArg(v_s_3963_, v___x_3966_);
v___x_3968_ = l_Lean_Syntax_getId(v_src_3967_);
v___x_3969_ = l_Lean_extractMacroScopes(v___x_3968_);
v_imported_3970_ = lean_ctor_get(v___x_3969_, 1);
v_ctx_3971_ = lean_ctor_get(v___x_3969_, 2);
v_scopes_3972_ = lean_ctor_get(v___x_3969_, 3);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3969_, 0);
lean_dec(v_unused_3989_);
v___x_3974_ = v___x_3969_;
v_isShared_3975_ = v_isSharedCheck_3988_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_scopes_3972_);
lean_inc(v_ctx_3971_);
lean_inc(v_imported_3970_);
lean_dec(v___x_3969_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3988_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = l_Lean_Name_eraseMacroScopes(v_val_3964_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3976_);
v___x_3978_ = v___x_3974_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3976_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_imported_3970_);
lean_ctor_set(v_reuseFailAlloc_3987_, 2, v_ctx_3971_);
lean_ctor_set(v_reuseFailAlloc_3987_, 3, v_scopes_3972_);
v___x_3978_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v_id_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_id_3979_ = l_Lean_MacroScopesView_review(v___x_3978_);
v___x_3980_ = l_Lean_SourceInfo_fromRef(v_src_3967_, v_canonical_3965_);
lean_dec(v_src_3967_);
v___x_3981_ = 1;
v___x_3982_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3964_, v___x_3981_);
v___x_3983_ = lean_string_utf8_byte_size(v___x_3982_);
v___x_3984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set(v___x_3984_, 1, v___x_3966_);
lean_ctor_set(v___x_3984_, 2, v___x_3983_);
v___x_3985_ = lean_box(0);
v___x_3986_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3980_);
lean_ctor_set(v___x_3986_, 1, v___x_3984_);
lean_ctor_set(v___x_3986_, 2, v_id_3979_);
lean_ctor_set(v___x_3986_, 3, v___x_3985_);
return v___x_3986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_3990_, lean_object* v_val_3991_, lean_object* v_canonical_3992_){
_start:
{
uint8_t v_canonical_boxed_3993_; lean_object* v_res_3994_; 
v_canonical_boxed_3993_ = lean_unbox(v_canonical_3992_);
v_res_3994_ = l_Lean_HygieneInfo_mkIdent(v_s_3990_, v_val_3991_, v_canonical_boxed_3993_);
lean_dec(v_s_3990_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_3995_, lean_object* v_inst_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_apply_1(v_inst_3995_, v_a_3997_);
v___x_3999_ = lean_apply_1(v_inst_3996_, v___x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4000_, lean_object* v_inst_4001_){
_start:
{
lean_object* v___f_4002_; 
v___f_4002_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4002_, 0, v_inst_4000_);
lean_closure_set(v___f_4002_, 1, v_inst_4001_);
return v___f_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4003_, lean_object* v_k_4004_, lean_object* v_k_x27_4005_, lean_object* v_inst_4006_, lean_object* v_inst_4007_){
_start:
{
lean_object* v___f_4008_; 
v___f_4008_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4008_, 0, v_inst_4006_);
lean_closure_set(v___f_4008_, 1, v_inst_4007_);
return v___f_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4009_, lean_object* v_k_4010_, lean_object* v_k_x27_4011_, lean_object* v_inst_4012_, lean_object* v_inst_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4009_, v_k_4010_, v_k_x27_4011_, v_inst_4012_, v_inst_4013_);
lean_dec(v_k_x27_4011_);
lean_dec(v_k_4010_);
return v_res_4014_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4023_ = l_Lean_mkCIdent(v___x_4022_);
return v___x_4023_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4029_ = l_Lean_mkCIdent(v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4030_){
_start:
{
if (v_x_4030_ == 0)
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4031_;
}
else
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4033_){
_start:
{
uint8_t v_x_85__boxed_4034_; lean_object* v_res_4035_; 
v_x_85__boxed_4034_ = lean_unbox(v_x_4033_);
v_res_4035_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4034_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4038_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_box(2);
v___x_4040_ = l_Lean_Syntax_mkCharLit(v_val_4038_, v___x_4039_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4041_){
_start:
{
uint32_t v_val_boxed_4042_; lean_object* v_res_4043_; 
v_val_boxed_4042_ = lean_unbox_uint32(v_val_4041_);
lean_dec(v_val_4041_);
v_res_4043_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4042_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4046_){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_box(2);
v___x_4048_ = l_Lean_Syntax_mkStrLit(v_val_4046_, v___x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4051_){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = l_Nat_reprFast(v_n_4051_);
v___x_4053_ = lean_box(2);
v___x_4054_ = l_Lean_Syntax_mkNumLit(v___x_4052_, v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4062_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4063_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4064_ = lean_substring_tostring(v_s_4062_);
v___x_4065_ = lean_box(2);
v___x_4066_ = l_Lean_Syntax_mkStrLit(v___x_4064_, v___x_4065_);
v___x_4067_ = lean_unsigned_to_nat(1u);
v___x_4068_ = lean_mk_empty_array_with_capacity(v___x_4067_);
v___x_4069_ = lean_array_push(v___x_4068_, v___x_4066_);
v___x_4070_ = l_Lean_Syntax_mkCApp(v___x_4063_, v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4073_, lean_object* v_x_4074_){
_start:
{
switch(lean_obj_tag(v_x_4074_))
{
case 0:
{
uint8_t v___x_4075_; 
v___x_4075_ = l_List_isEmpty___redArg(v_acc_4073_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; 
v___x_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4076_, 0, v_acc_4073_);
return v___x_4076_;
}
else
{
lean_object* v___x_4077_; 
lean_dec(v_acc_4073_);
v___x_4077_ = lean_box(0);
return v___x_4077_;
}
}
case 1:
{
lean_object* v_pre_4078_; lean_object* v_str_4079_; lean_object* v_val_4081_; lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v_pre_4078_ = lean_ctor_get(v_x_4074_, 0);
lean_inc(v_pre_4078_);
v_str_4079_ = lean_ctor_get(v_x_4074_, 1);
lean_inc_ref(v_str_4079_);
lean_dec_ref_known(v_x_4074_, 2);
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = lean_string_utf8_byte_size(v_str_4079_);
v___x_4086_ = lean_nat_dec_lt(v___x_4084_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4087_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4088_ = lean_string_append(v___x_4087_, v_str_4079_);
lean_dec_ref(v_str_4079_);
v___x_4089_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4090_ = lean_string_append(v___x_4088_, v___x_4089_);
v_val_4081_ = v___x_4090_;
goto v___jp_4080_;
}
else
{
lean_object* v___f_4091_; uint8_t v___y_4093_; lean_object* v___f_4100_; uint32_t v___y_4107_; uint32_t v___y_4112_; uint8_t v___y_4113_; uint8_t v_c_4127_; uint8_t v___x_4136_; uint8_t v___x_4137_; 
v___f_4091_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4100_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4127_ = lean_string_get_byte_fast(v_str_4079_, v___x_4084_);
v___x_4136_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4137_ = lean_uint8_dec_le(v___x_4136_, v_c_4127_);
if (v___x_4137_ == 0)
{
goto v___jp_4131_;
}
else
{
uint8_t v___x_4138_; uint8_t v___x_4139_; 
v___x_4138_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
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
v___jp_4092_:
{
if (v___y_4093_ == 0)
{
uint8_t v___x_4094_; 
lean_inc_ref(v_str_4079_);
v___x_4094_ = lean_string_any(v_str_4079_, v___f_4091_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4095_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4096_ = lean_string_append(v___x_4095_, v_str_4079_);
lean_dec_ref(v_str_4079_);
v___x_4097_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4098_ = lean_string_append(v___x_4096_, v___x_4097_);
v_val_4081_ = v___x_4098_;
goto v___jp_4080_;
}
else
{
lean_object* v___x_4099_; 
lean_dec_ref(v_str_4079_);
lean_dec(v_pre_4078_);
lean_dec(v_acc_4073_);
v___x_4099_ = lean_box(0);
return v___x_4099_;
}
}
else
{
v_val_4081_ = v_str_4079_;
goto v___jp_4080_;
}
}
v___jp_4101_:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
lean_inc_ref(v_str_4079_);
v___x_4102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4102_, 0, v_str_4079_);
lean_ctor_set(v___x_4102_, 1, v___x_4084_);
lean_ctor_set(v___x_4102_, 2, v___x_4085_);
v___x_4103_ = lean_unsigned_to_nat(1u);
v___x_4104_ = lean_substring_drop(v___x_4102_, v___x_4103_);
v___x_4105_ = lean_substring_all(v___x_4104_, v___f_4100_);
v___y_4093_ = v___x_4105_;
goto v___jp_4092_;
}
v___jp_4106_:
{
uint32_t v___x_4108_; uint8_t v___x_4109_; 
v___x_4108_ = 95;
v___x_4109_ = lean_uint32_dec_eq(v___y_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
uint8_t v___x_4110_; 
v___x_4110_ = l_Lean_isLetterLike(v___y_4107_);
if (v___x_4110_ == 0)
{
v___y_4093_ = v___x_4110_;
goto v___jp_4092_;
}
else
{
goto v___jp_4101_;
}
}
else
{
goto v___jp_4101_;
}
}
v___jp_4111_:
{
if (v___y_4113_ == 0)
{
uint32_t v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = 97;
v___x_4115_ = lean_uint32_dec_le(v___x_4114_, v___y_4112_);
if (v___x_4115_ == 0)
{
v___y_4107_ = v___y_4112_;
goto v___jp_4106_;
}
else
{
uint32_t v___x_4116_; uint8_t v___x_4117_; 
v___x_4116_ = 122;
v___x_4117_ = lean_uint32_dec_le(v___y_4112_, v___x_4116_);
if (v___x_4117_ == 0)
{
v___y_4107_ = v___y_4112_;
goto v___jp_4106_;
}
else
{
goto v___jp_4101_;
}
}
}
else
{
goto v___jp_4101_;
}
}
v___jp_4118_:
{
uint32_t v___x_4119_; uint32_t v___x_4120_; uint8_t v___x_4121_; 
v___x_4119_ = lean_string_utf8_get(v_str_4079_, v___x_4084_);
v___x_4120_ = 65;
v___x_4121_ = lean_uint32_dec_le(v___x_4120_, v___x_4119_);
if (v___x_4121_ == 0)
{
v___y_4112_ = v___x_4119_;
v___y_4113_ = v___x_4121_;
goto v___jp_4111_;
}
else
{
uint32_t v___x_4122_; uint8_t v___x_4123_; 
v___x_4122_ = 90;
v___x_4123_ = lean_uint32_dec_le(v___x_4119_, v___x_4122_);
v___y_4112_ = v___x_4119_;
v___y_4113_ = v___x_4123_;
goto v___jp_4111_;
}
}
v___jp_4124_:
{
lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4125_ = lean_unsigned_to_nat(1u);
v___x_4126_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4079_, v___x_4125_);
if (v___x_4126_ == 0)
{
goto v___jp_4118_;
}
else
{
v___y_4093_ = v___x_4126_;
goto v___jp_4092_;
}
}
v___jp_4128_:
{
uint8_t v___x_4129_; uint8_t v___x_4130_; 
v___x_4129_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
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
v___x_4132_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4133_ = lean_uint8_dec_le(v___x_4132_, v_c_4127_);
if (v___x_4133_ == 0)
{
goto v___jp_4128_;
}
else
{
uint8_t v___x_4134_; uint8_t v___x_4135_; 
v___x_4134_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
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
v___jp_4080_:
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4082_, 0, v_val_4081_);
lean_ctor_set(v___x_4082_, 1, v_acc_4073_);
v_acc_4073_ = v___x_4082_;
v_x_4074_ = v_pre_4078_;
goto _start;
}
}
default: 
{
lean_object* v___x_4140_; 
lean_dec_ref_known(v_x_4074_, 2);
lean_dec(v_acc_4073_);
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
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4388_, lean_object* v_k_4389_){
_start:
{
lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4391_ = lean_name_eq(v_k_4389_, v___x_4390_);
if (v___x_4391_ == 0)
{
uint8_t v___x_4392_; 
v___x_4392_ = 1;
return v___x_4392_;
}
else
{
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4393_, lean_object* v_k_4394_){
_start:
{
uint8_t v___x_442__boxed_4395_; uint8_t v_res_4396_; lean_object* v_r_4397_; 
v___x_442__boxed_4395_ = lean_unbox(v___x_4393_);
v_res_4396_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4395_, v_k_4394_);
lean_dec(v_k_4394_);
v_r_4397_ = lean_box(v_res_4396_);
return v_r_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_methods_4402_; lean_object* v_quotContext_4403_; lean_object* v_currMacroScope_4404_; lean_object* v_currRecDepth_4405_; lean_object* v_maxRecDepth_4406_; lean_object* v_ref_4407_; uint8_t v___x_4408_; 
v_methods_4402_ = lean_ctor_get(v_a_4400_, 0);
v_quotContext_4403_ = lean_ctor_get(v_a_4400_, 1);
v_currMacroScope_4404_ = lean_ctor_get(v_a_4400_, 2);
v_currRecDepth_4405_ = lean_ctor_get(v_a_4400_, 3);
v_maxRecDepth_4406_ = lean_ctor_get(v_a_4400_, 4);
v_ref_4407_ = lean_ctor_get(v_a_4400_, 5);
v___x_4408_ = lean_nat_dec_eq(v_currRecDepth_4405_, v_maxRecDepth_4406_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4409_ = lean_box(v___x_4408_);
v___f_4410_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4410_, 0, v___x_4409_);
v___x_4411_ = lean_unsigned_to_nat(1u);
v___x_4412_ = lean_nat_add(v_currRecDepth_4405_, v___x_4411_);
lean_inc(v_ref_4407_);
lean_inc(v_maxRecDepth_4406_);
lean_inc(v_currMacroScope_4404_);
lean_inc(v_quotContext_4403_);
lean_inc(v_methods_4402_);
v___x_4413_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4413_, 0, v_methods_4402_);
lean_ctor_set(v___x_4413_, 1, v_quotContext_4403_);
lean_ctor_set(v___x_4413_, 2, v_currMacroScope_4404_);
lean_ctor_set(v___x_4413_, 3, v___x_4412_);
lean_ctor_set(v___x_4413_, 4, v_maxRecDepth_4406_);
lean_ctor_set(v___x_4413_, 5, v_ref_4407_);
lean_inc_ref(v___x_4413_);
v___x_4414_ = l_Lean_expandMacros(v_stx_4399_, v___f_4410_, v___x_4413_, v_a_4401_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4428_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_a_4416_ = lean_ctor_get(v___x_4414_, 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4418_ = v___x_4414_;
v_isShared_4419_ = v_isSharedCheck_4428_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4428_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4420_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4415_);
v___x_4421_ = l_Lean_Syntax_isOfKind(v_a_4415_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_del_object(v___x_4418_);
v___x_4422_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4423_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4415_, v___x_4422_, v___x_4413_, v_a_4416_);
lean_dec_ref_known(v___x_4413_, 6);
lean_dec(v_a_4415_);
return v___x_4423_;
}
else
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
lean_dec_ref_known(v___x_4413_, 6);
v___x_4424_ = l_Lean_TSyntax_getNat(v_a_4415_);
lean_dec(v_a_4415_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4424_);
v___x_4426_ = v___x_4418_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_a_4416_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
else
{
lean_object* v_a_4429_; lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref_known(v___x_4413_, 6);
v_a_4429_ = lean_ctor_get(v___x_4414_, 0);
v_a_4430_ = lean_ctor_get(v___x_4414_, 1);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4414_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_inc(v_a_4429_);
lean_dec(v___x_4414_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4429_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4439_, 0, v_stx_4399_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
lean_ctor_set(v___x_4440_, 1, v_a_4401_);
return v___x_4440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_evalPrec(v_stx_4441_, v_a_4442_, v_a_4443_);
lean_dec_ref(v_a_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
lean_object* v_methods_4449_; lean_object* v_quotContext_4450_; lean_object* v_currMacroScope_4451_; lean_object* v_currRecDepth_4452_; lean_object* v_maxRecDepth_4453_; lean_object* v_ref_4454_; uint8_t v___x_4455_; 
v_methods_4449_ = lean_ctor_get(v_a_4447_, 0);
v_quotContext_4450_ = lean_ctor_get(v_a_4447_, 1);
v_currMacroScope_4451_ = lean_ctor_get(v_a_4447_, 2);
v_currRecDepth_4452_ = lean_ctor_get(v_a_4447_, 3);
v_maxRecDepth_4453_ = lean_ctor_get(v_a_4447_, 4);
v_ref_4454_ = lean_ctor_get(v_a_4447_, 5);
v___x_4455_ = lean_nat_dec_eq(v_currRecDepth_4452_, v_maxRecDepth_4453_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v___f_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4456_ = lean_box(v___x_4455_);
v___f_4457_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4457_, 0, v___x_4456_);
v___x_4458_ = lean_unsigned_to_nat(1u);
v___x_4459_ = lean_nat_add(v_currRecDepth_4452_, v___x_4458_);
lean_inc(v_ref_4454_);
lean_inc(v_maxRecDepth_4453_);
lean_inc(v_currMacroScope_4451_);
lean_inc(v_quotContext_4450_);
lean_inc(v_methods_4449_);
v___x_4460_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4460_, 0, v_methods_4449_);
lean_ctor_set(v___x_4460_, 1, v_quotContext_4450_);
lean_ctor_set(v___x_4460_, 2, v_currMacroScope_4451_);
lean_ctor_set(v___x_4460_, 3, v___x_4459_);
lean_ctor_set(v___x_4460_, 4, v_maxRecDepth_4453_);
lean_ctor_set(v___x_4460_, 5, v_ref_4454_);
lean_inc_ref(v___x_4460_);
v___x_4461_ = l_Lean_expandMacros(v_stx_4446_, v___f_4457_, v___x_4460_, v_a_4448_);
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
v___x_4469_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4470_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4462_, v___x_4469_, v___x_4460_, v_a_4463_);
lean_dec_ref_known(v___x_4460_, 6);
lean_dec(v_a_4462_);
return v___x_4470_;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
lean_dec_ref_known(v___x_4460_, 6);
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
lean_dec_ref_known(v___x_4460_, 6);
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
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4485_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4486_, 0, v_stx_4446_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
lean_ctor_set(v___x_4487_, 1, v_a_4448_);
return v___x_4487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_evalPrio(v_stx_4488_, v_a_4489_, v_a_4490_);
lean_dec_ref(v_a_4489_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
if (lean_obj_tag(v_x_4492_) == 0)
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = lean_unsigned_to_nat(1000u);
v___x_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
lean_ctor_set(v___x_4496_, 1, v_a_4494_);
return v___x_4496_;
}
else
{
lean_object* v_val_4497_; lean_object* v___x_4498_; 
v_val_4497_ = lean_ctor_get(v_x_4492_, 0);
lean_inc(v_val_4497_);
lean_dec_ref_known(v_x_4492_, 1);
v___x_4498_ = l_Lean_evalPrio(v_val_4497_, v_a_4493_, v_a_4494_);
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_evalOptPrio(v_x_4499_, v_a_4500_, v_a_4501_);
lean_dec_ref(v_a_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4503_, lean_object* v_x1_4504_, lean_object* v_x2_4505_){
_start:
{
lean_object* v_fst_4506_; uint8_t v___x_4507_; 
v_fst_4506_ = lean_ctor_get(v_x1_4504_, 0);
v___x_4507_ = lean_unbox(v_fst_4506_);
if (v___x_4507_ == 0)
{
lean_object* v_snd_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_x2_4505_);
v_snd_4508_ = lean_ctor_get(v_x1_4504_, 1);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_x1_4504_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; 
v_unused_4517_ = lean_ctor_get(v_x1_4504_, 0);
lean_dec(v_unused_4517_);
v___x_4510_ = v_x1_4504_;
v_isShared_4511_ = v_isSharedCheck_4516_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_snd_4508_);
lean_dec(v_x1_4504_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4516_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4512_ = lean_box(v___x_4503_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4512_);
v___x_4514_ = v___x_4510_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_snd_4508_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
else
{
lean_object* v_snd_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4528_; 
v_snd_4518_ = lean_ctor_get(v_x1_4504_, 1);
v_isSharedCheck_4528_ = !lean_is_exclusive(v_x1_4504_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v_x1_4504_, 0);
lean_dec(v_unused_4529_);
v___x_4520_ = v_x1_4504_;
v_isShared_4521_ = v_isSharedCheck_4528_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_snd_4518_);
lean_dec(v_x1_4504_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4528_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4522_ = 0;
v___x_4523_ = lean_array_push(v_snd_4518_, v_x2_4505_);
v___x_4524_ = lean_box(v___x_4522_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 1, v___x_4523_);
lean_ctor_set(v___x_4520_, 0, v___x_4524_);
v___x_4526_ = v___x_4520_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4523_);
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
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4530_, lean_object* v_x1_4531_, lean_object* v_x2_4532_){
_start:
{
uint8_t v___x_87__boxed_4533_; lean_object* v_res_4534_; 
v___x_87__boxed_4533_ = lean_unbox(v___x_4530_);
v_res_4534_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4533_, v_x1_4531_, v_x2_4532_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4556_){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; uint8_t v___x_4561_; 
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4559_ = lean_array_get_size(v_as_4556_);
v___x_4560_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4561_ = lean_nat_dec_lt(v___x_4557_, v___x_4559_);
if (v___x_4561_ == 0)
{
lean_dec_ref(v_as_4556_);
return v___x_4558_;
}
else
{
lean_object* v___x_4562_; lean_object* v___f_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; size_t v___x_4566_; size_t v___x_4567_; lean_object* v___x_4568_; lean_object* v_snd_4569_; 
v___x_4562_ = lean_box(v___x_4561_);
v___f_4563_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4563_, 0, v___x_4562_);
v___x_4564_ = lean_box(v___x_4561_);
v___x_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
lean_ctor_set(v___x_4565_, 1, v___x_4558_);
v___x_4566_ = ((size_t)0ULL);
v___x_4567_ = lean_usize_of_nat(v___x_4559_);
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4560_, v___f_4563_, v_as_4556_, v___x_4566_, v___x_4567_, v___x_4565_);
v_snd_4569_ = lean_ctor_get(v___x_4568_, 1);
lean_inc(v_snd_4569_);
lean_dec(v___x_4568_);
return v_snd_4569_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4570_, lean_object* v_as_4571_){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; 
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4573_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4574_ = lean_array_get_size(v_as_4571_);
v___x_4575_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4576_ = lean_nat_dec_lt(v___x_4572_, v___x_4574_);
if (v___x_4576_ == 0)
{
lean_dec_ref(v_as_4571_);
return v___x_4573_;
}
else
{
lean_object* v___x_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; size_t v___x_4581_; size_t v___x_4582_; lean_object* v___x_4583_; lean_object* v_snd_4584_; 
v___x_4577_ = lean_box(v___x_4576_);
v___f_4578_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4578_, 0, v___x_4577_);
v___x_4579_ = lean_box(v___x_4576_);
v___x_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v___x_4573_);
v___x_4581_ = ((size_t)0ULL);
v___x_4582_ = lean_usize_of_nat(v___x_4574_);
v___x_4583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4575_, v___f_4578_, v_as_4571_, v___x_4581_, v___x_4582_, v___x_4580_);
v_snd_4584_ = lean_ctor_get(v___x_4583_, 1);
lean_inc(v_snd_4584_);
lean_dec(v___x_4583_);
return v_snd_4584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4585_, lean_object* v_inst_4586_, lean_object* v_a_4587_, lean_object* v_p_4588_, lean_object* v_acc_4589_, lean_object* v_stx_4590_, uint8_t v_____do__lift_4591_){
_start:
{
if (v_____do__lift_4591_ == 0)
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
lean_dec(v_stx_4590_);
v___x_4600_ = lean_unsigned_to_nat(2u);
v___x_4601_ = lean_nat_add(v_i_4585_, v___x_4600_);
v___x_4602_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4586_, v_a_4587_, v_p_4588_, v___x_4601_, v_acc_4589_);
return v___x_4602_;
}
else
{
lean_object* v___x_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4603_ = lean_array_get_size(v_acc_4589_);
v___x_4604_ = lean_unsigned_to_nat(0u);
v___x_4605_ = lean_nat_dec_eq(v___x_4603_, v___x_4604_);
if (v___x_4605_ == 0)
{
uint8_t v___x_4606_; 
v___x_4606_ = lean_nat_dec_eq(v_i_4585_, v___x_4604_);
if (v___x_4606_ == 0)
{
goto v___jp_4592_;
}
else
{
if (v___x_4605_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4607_ = lean_unsigned_to_nat(2u);
v___x_4608_ = lean_nat_add(v_i_4585_, v___x_4607_);
v___x_4609_ = lean_array_push(v_acc_4589_, v_stx_4590_);
v___x_4610_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4586_, v_a_4587_, v_p_4588_, v___x_4608_, v___x_4609_);
return v___x_4610_;
}
else
{
goto v___jp_4592_;
}
}
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4611_ = lean_unsigned_to_nat(2u);
v___x_4612_ = lean_nat_add(v_i_4585_, v___x_4611_);
v___x_4613_ = lean_array_push(v_acc_4589_, v_stx_4590_);
v___x_4614_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4586_, v_a_4587_, v_p_4588_, v___x_4612_, v___x_4613_);
return v___x_4614_;
}
}
v___jp_4592_:
{
lean_object* v___x_4593_; lean_object* v_sepStx_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4593_ = lean_nat_pred(v_i_4585_);
v_sepStx_4594_ = lean_array_fget_borrowed(v_a_4587_, v___x_4593_);
lean_dec(v___x_4593_);
v___x_4595_ = lean_unsigned_to_nat(2u);
v___x_4596_ = lean_nat_add(v_i_4585_, v___x_4595_);
lean_inc(v_sepStx_4594_);
v___x_4597_ = lean_array_push(v_acc_4589_, v_sepStx_4594_);
v___x_4598_ = lean_array_push(v___x_4597_, v_stx_4590_);
v___x_4599_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4586_, v_a_4587_, v_p_4588_, v___x_4596_, v___x_4598_);
return v___x_4599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4615_, lean_object* v_inst_4616_, lean_object* v_a_4617_, lean_object* v_p_4618_, lean_object* v_acc_4619_, lean_object* v_stx_4620_, lean_object* v_____do__lift_4621_){
_start:
{
uint8_t v_____do__lift_208__boxed_4622_; lean_object* v_res_4623_; 
v_____do__lift_208__boxed_4622_ = lean_unbox(v_____do__lift_4621_);
v_res_4623_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4615_, v_inst_4616_, v_a_4617_, v_p_4618_, v_acc_4619_, v_stx_4620_, v_____do__lift_208__boxed_4622_);
lean_dec(v_i_4615_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4624_, lean_object* v_a_4625_, lean_object* v_p_4626_, lean_object* v_i_4627_, lean_object* v_acc_4628_){
_start:
{
lean_object* v_toApplicative_4629_; lean_object* v_toBind_4630_; lean_object* v_toPure_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; 
v_toApplicative_4629_ = lean_ctor_get(v_inst_4624_, 0);
v_toBind_4630_ = lean_ctor_get(v_inst_4624_, 1);
lean_inc(v_toBind_4630_);
v_toPure_4631_ = lean_ctor_get(v_toApplicative_4629_, 1);
v___x_4632_ = lean_array_get_size(v_a_4625_);
v___x_4633_ = lean_nat_dec_lt(v_i_4627_, v___x_4632_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; 
lean_inc(v_toPure_4631_);
lean_dec(v_toBind_4630_);
lean_dec(v_i_4627_);
lean_dec(v_p_4626_);
lean_dec_ref(v_a_4625_);
lean_dec_ref(v_inst_4624_);
v___x_4634_ = lean_apply_2(v_toPure_4631_, lean_box(0), v_acc_4628_);
return v___x_4634_;
}
else
{
lean_object* v_stx_4635_; lean_object* v___f_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v_stx_4635_ = lean_array_fget(v_a_4625_, v_i_4627_);
lean_inc(v_stx_4635_);
lean_inc(v_p_4626_);
v___f_4636_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4636_, 0, v_i_4627_);
lean_closure_set(v___f_4636_, 1, v_inst_4624_);
lean_closure_set(v___f_4636_, 2, v_a_4625_);
lean_closure_set(v___f_4636_, 3, v_p_4626_);
lean_closure_set(v___f_4636_, 4, v_acc_4628_);
lean_closure_set(v___f_4636_, 5, v_stx_4635_);
v___x_4637_ = lean_apply_1(v_p_4626_, v_stx_4635_);
v___x_4638_ = lean_apply_4(v_toBind_4630_, lean_box(0), lean_box(0), v___x_4637_, v___f_4636_);
return v___x_4638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4639_, lean_object* v_inst_4640_, lean_object* v_a_4641_, lean_object* v_p_4642_, lean_object* v_i_4643_, lean_object* v_acc_4644_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4640_, v_a_4641_, v_p_4642_, v_i_4643_, v_acc_4644_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4646_, lean_object* v_a_4647_, lean_object* v_p_4648_){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4651_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4646_, v_a_4647_, v_p_4648_, v___x_4649_, v___x_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4652_, lean_object* v_inst_4653_, lean_object* v_a_4654_, lean_object* v_p_4655_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Array_filterSepElemsM___redArg(v_inst_4653_, v_a_4654_, v_p_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4657_, lean_object* v_x_4658_){
_start:
{
lean_object* v___x_4659_; uint8_t v___x_4660_; 
v___x_4659_ = lean_apply_1(v_p_4657_, v_x_4658_);
v___x_4660_ = lean_unbox(v___x_4659_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4661_, lean_object* v_x_4662_){
_start:
{
uint8_t v_res_4663_; lean_object* v_r_4664_; 
v_res_4663_ = l_Array_filterSepElems___lam__0(v_p_4661_, v_x_4662_);
v_r_4664_ = lean_box(v_res_4663_);
return v_r_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4665_, lean_object* v_p_4666_, lean_object* v_i_4667_, lean_object* v_acc_4668_){
_start:
{
lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4669_ = lean_array_get_size(v_a_4665_);
v___x_4670_ = lean_nat_dec_lt(v_i_4667_, v___x_4669_);
if (v___x_4670_ == 0)
{
lean_dec(v_i_4667_);
lean_dec_ref(v_p_4666_);
return v_acc_4668_;
}
else
{
lean_object* v_stx_4671_; lean_object* v___x_4680_; uint8_t v___x_4681_; 
v_stx_4671_ = lean_array_fget_borrowed(v_a_4665_, v_i_4667_);
lean_inc_ref(v_p_4666_);
lean_inc(v_stx_4671_);
v___x_4680_ = lean_apply_1(v_p_4666_, v_stx_4671_);
v___x_4681_ = lean_unbox(v___x_4680_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_unsigned_to_nat(2u);
v___x_4683_ = lean_nat_add(v_i_4667_, v___x_4682_);
lean_dec(v_i_4667_);
v_i_4667_ = v___x_4683_;
goto _start;
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; 
v___x_4685_ = lean_array_get_size(v_acc_4668_);
v___x_4686_ = lean_unsigned_to_nat(0u);
v___x_4687_ = lean_nat_dec_eq(v___x_4685_, v___x_4686_);
if (v___x_4687_ == 0)
{
uint8_t v___x_4688_; 
v___x_4688_ = lean_nat_dec_eq(v_i_4667_, v___x_4686_);
if (v___x_4688_ == 0)
{
goto v___jp_4672_;
}
else
{
if (v___x_4687_ == 0)
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4689_ = lean_unsigned_to_nat(2u);
v___x_4690_ = lean_nat_add(v_i_4667_, v___x_4689_);
lean_dec(v_i_4667_);
lean_inc(v_stx_4671_);
v___x_4691_ = lean_array_push(v_acc_4668_, v_stx_4671_);
v_i_4667_ = v___x_4690_;
v_acc_4668_ = v___x_4691_;
goto _start;
}
else
{
goto v___jp_4672_;
}
}
}
else
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4693_ = lean_unsigned_to_nat(2u);
v___x_4694_ = lean_nat_add(v_i_4667_, v___x_4693_);
lean_dec(v_i_4667_);
lean_inc(v_stx_4671_);
v___x_4695_ = lean_array_push(v_acc_4668_, v_stx_4671_);
v_i_4667_ = v___x_4694_;
v_acc_4668_ = v___x_4695_;
goto _start;
}
}
v___jp_4672_:
{
lean_object* v___x_4673_; lean_object* v_sepStx_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4673_ = lean_nat_pred(v_i_4667_);
v_sepStx_4674_ = lean_array_fget_borrowed(v_a_4665_, v___x_4673_);
lean_dec(v___x_4673_);
v___x_4675_ = lean_unsigned_to_nat(2u);
v___x_4676_ = lean_nat_add(v_i_4667_, v___x_4675_);
lean_dec(v_i_4667_);
lean_inc(v_sepStx_4674_);
v___x_4677_ = lean_array_push(v_acc_4668_, v_sepStx_4674_);
lean_inc(v_stx_4671_);
v___x_4678_ = lean_array_push(v___x_4677_, v_stx_4671_);
v_i_4667_ = v___x_4676_;
v_acc_4668_ = v___x_4678_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4697_, lean_object* v_p_4698_, lean_object* v_i_4699_, lean_object* v_acc_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4697_, v_p_4698_, v_i_4699_, v_acc_4700_);
lean_dec_ref(v_a_4697_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4702_, lean_object* v_p_4703_){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4704_ = lean_unsigned_to_nat(0u);
v___x_4705_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4706_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4702_, v_p_4703_, v___x_4704_, v___x_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4707_, lean_object* v_p_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4707_, v_p_4708_);
lean_dec_ref(v_a_4707_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4710_, lean_object* v_p_4711_){
_start:
{
lean_object* v___f_4712_; lean_object* v___x_4713_; 
v___f_4712_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4712_, 0, v_p_4711_);
v___x_4713_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4710_, v___f_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4714_, lean_object* v_p_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Array_filterSepElems(v_a_4714_, v_p_4715_);
lean_dec_ref(v_a_4714_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4717_, lean_object* v_acc_4718_, lean_object* v_inst_4719_, lean_object* v_a_4720_, lean_object* v_f_4721_, lean_object* v_stx_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4717_, v_acc_4718_, v_inst_4719_, v_a_4720_, v_f_4721_, v_stx_4722_);
lean_dec(v_i_4717_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4724_, lean_object* v_a_4725_, lean_object* v_f_4726_, lean_object* v_i_4727_, lean_object* v_acc_4728_){
_start:
{
lean_object* v_toApplicative_4729_; lean_object* v_toBind_4730_; lean_object* v_toPure_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v_toApplicative_4729_ = lean_ctor_get(v_inst_4724_, 0);
v_toBind_4730_ = lean_ctor_get(v_inst_4724_, 1);
v_toPure_4731_ = lean_ctor_get(v_toApplicative_4729_, 1);
v___x_4732_ = lean_array_get_size(v_a_4725_);
v___x_4733_ = lean_nat_dec_lt(v_i_4727_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; 
lean_inc(v_toPure_4731_);
lean_dec(v_i_4727_);
lean_dec(v_f_4726_);
lean_dec_ref(v_a_4725_);
lean_dec_ref(v_inst_4724_);
v___x_4734_ = lean_apply_2(v_toPure_4731_, lean_box(0), v_acc_4728_);
return v___x_4734_;
}
else
{
lean_object* v_stx_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; 
v_stx_4735_ = lean_array_fget_borrowed(v_a_4725_, v_i_4727_);
v___x_4736_ = lean_unsigned_to_nat(2u);
v___x_4737_ = lean_nat_mod(v_i_4727_, v___x_4736_);
v___x_4738_ = lean_unsigned_to_nat(0u);
v___x_4739_ = lean_nat_dec_eq(v___x_4737_, v___x_4738_);
lean_dec(v___x_4737_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = lean_unsigned_to_nat(1u);
v___x_4741_ = lean_nat_add(v_i_4727_, v___x_4740_);
lean_dec(v_i_4727_);
lean_inc(v_stx_4735_);
v___x_4742_ = lean_array_push(v_acc_4728_, v_stx_4735_);
v_i_4727_ = v___x_4741_;
v_acc_4728_ = v___x_4742_;
goto _start;
}
else
{
lean_object* v___f_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
lean_inc(v_stx_4735_);
lean_inc(v_toBind_4730_);
lean_inc(v_f_4726_);
v___f_4744_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4744_, 0, v_i_4727_);
lean_closure_set(v___f_4744_, 1, v_acc_4728_);
lean_closure_set(v___f_4744_, 2, v_inst_4724_);
lean_closure_set(v___f_4744_, 3, v_a_4725_);
lean_closure_set(v___f_4744_, 4, v_f_4726_);
v___x_4745_ = lean_apply_1(v_f_4726_, v_stx_4735_);
v___x_4746_ = lean_apply_4(v_toBind_4730_, lean_box(0), lean_box(0), v___x_4745_, v___f_4744_);
return v___x_4746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4747_, lean_object* v_acc_4748_, lean_object* v_inst_4749_, lean_object* v_a_4750_, lean_object* v_f_4751_, lean_object* v_stx_4752_){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4753_ = lean_unsigned_to_nat(1u);
v___x_4754_ = lean_nat_add(v_i_4747_, v___x_4753_);
v___x_4755_ = lean_array_push(v_acc_4748_, v_stx_4752_);
v___x_4756_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4749_, v_a_4750_, v_f_4751_, v___x_4754_, v___x_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4757_, lean_object* v_inst_4758_, lean_object* v_a_4759_, lean_object* v_f_4760_, lean_object* v_i_4761_, lean_object* v_acc_4762_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4758_, v_a_4759_, v_f_4760_, v_i_4761_, v_acc_4762_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4764_, lean_object* v_a_4765_, lean_object* v_f_4766_){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4767_ = lean_unsigned_to_nat(0u);
v___x_4768_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4769_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4764_, v_a_4765_, v_f_4766_, v___x_4767_, v___x_4768_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4770_, lean_object* v_inst_4771_, lean_object* v_a_4772_, lean_object* v_f_4773_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_Array_mapSepElemsM___redArg(v_inst_4771_, v_a_4772_, v_f_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4775_, lean_object* v_x_4776_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = lean_apply_1(v_f_4775_, v_x_4776_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4778_, lean_object* v_f_4779_, lean_object* v_i_4780_, lean_object* v_acc_4781_){
_start:
{
lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4782_ = lean_array_get_size(v_a_4778_);
v___x_4783_ = lean_nat_dec_lt(v_i_4780_, v___x_4782_);
if (v___x_4783_ == 0)
{
lean_dec(v_i_4780_);
lean_dec_ref(v_f_4779_);
return v_acc_4781_;
}
else
{
lean_object* v_stx_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v_stx_4784_ = lean_array_fget_borrowed(v_a_4778_, v_i_4780_);
v___x_4785_ = lean_unsigned_to_nat(2u);
v___x_4786_ = lean_nat_mod(v_i_4780_, v___x_4785_);
v___x_4787_ = lean_unsigned_to_nat(0u);
v___x_4788_ = lean_nat_dec_eq(v___x_4786_, v___x_4787_);
lean_dec(v___x_4786_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = lean_unsigned_to_nat(1u);
v___x_4790_ = lean_nat_add(v_i_4780_, v___x_4789_);
lean_dec(v_i_4780_);
lean_inc(v_stx_4784_);
v___x_4791_ = lean_array_push(v_acc_4781_, v_stx_4784_);
v_i_4780_ = v___x_4790_;
v_acc_4781_ = v___x_4791_;
goto _start;
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_inc_ref(v_f_4779_);
lean_inc(v_stx_4784_);
v___x_4793_ = lean_apply_1(v_f_4779_, v_stx_4784_);
v___x_4794_ = lean_unsigned_to_nat(1u);
v___x_4795_ = lean_nat_add(v_i_4780_, v___x_4794_);
lean_dec(v_i_4780_);
v___x_4796_ = lean_array_push(v_acc_4781_, v___x_4793_);
v_i_4780_ = v___x_4795_;
v_acc_4781_ = v___x_4796_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4798_, lean_object* v_f_4799_, lean_object* v_i_4800_, lean_object* v_acc_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4798_, v_f_4799_, v_i_4800_, v_acc_4801_);
lean_dec_ref(v_a_4798_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4803_, lean_object* v_f_4804_){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4805_ = lean_unsigned_to_nat(0u);
v___x_4806_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4807_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4803_, v_f_4804_, v___x_4805_, v___x_4806_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4808_, lean_object* v_f_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4808_, v_f_4809_);
lean_dec_ref(v_a_4808_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4811_, lean_object* v_f_4812_){
_start:
{
lean_object* v___f_4813_; lean_object* v___x_4814_; 
v___f_4813_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4813_, 0, v_f_4812_);
v___x_4814_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4811_, v___f_4813_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4815_, lean_object* v_f_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Array_mapSepElems(v_a_4815_, v_f_4816_);
lean_dec_ref(v_a_4815_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4818_, size_t v_i_4819_, size_t v_stop_4820_, lean_object* v_b_4821_){
_start:
{
lean_object* v___y_4823_; uint8_t v___x_4827_; 
v___x_4827_ = lean_usize_dec_eq(v_i_4819_, v_stop_4820_);
if (v___x_4827_ == 0)
{
lean_object* v_fst_4828_; uint8_t v___x_4829_; 
v_fst_4828_ = lean_ctor_get(v_b_4821_, 0);
v___x_4829_ = lean_unbox(v_fst_4828_);
if (v___x_4829_ == 0)
{
lean_object* v_snd_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4839_; 
v_snd_4830_ = lean_ctor_get(v_b_4821_, 1);
v_isSharedCheck_4839_ = !lean_is_exclusive(v_b_4821_);
if (v_isSharedCheck_4839_ == 0)
{
lean_object* v_unused_4840_; 
v_unused_4840_ = lean_ctor_get(v_b_4821_, 0);
lean_dec(v_unused_4840_);
v___x_4832_ = v_b_4821_;
v_isShared_4833_ = v_isSharedCheck_4839_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_snd_4830_);
lean_dec(v_b_4821_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4839_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
uint8_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4834_ = 1;
v___x_4835_ = lean_box(v___x_4834_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4835_);
v___x_4837_ = v___x_4832_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_snd_4830_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
v___y_4823_ = v___x_4837_;
goto v___jp_4822_;
}
}
}
else
{
lean_object* v_snd_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4851_; 
v_snd_4841_ = lean_ctor_get(v_b_4821_, 1);
v_isSharedCheck_4851_ = !lean_is_exclusive(v_b_4821_);
if (v_isSharedCheck_4851_ == 0)
{
lean_object* v_unused_4852_; 
v_unused_4852_ = lean_ctor_get(v_b_4821_, 0);
lean_dec(v_unused_4852_);
v___x_4843_ = v_b_4821_;
v_isShared_4844_ = v_isSharedCheck_4851_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_snd_4841_);
lean_dec(v_b_4821_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4851_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4845_ = lean_array_uget_borrowed(v_as_4818_, v_i_4819_);
lean_inc(v___x_4845_);
v___x_4846_ = lean_array_push(v_snd_4841_, v___x_4845_);
v___x_4847_ = lean_box(v___x_4827_);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 1, v___x_4846_);
lean_ctor_set(v___x_4843_, 0, v___x_4847_);
v___x_4849_ = v___x_4843_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v___x_4846_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
v___y_4823_ = v___x_4849_;
goto v___jp_4822_;
}
}
}
}
else
{
return v_b_4821_;
}
v___jp_4822_:
{
size_t v___x_4824_; size_t v___x_4825_; 
v___x_4824_ = ((size_t)1ULL);
v___x_4825_ = lean_usize_add(v_i_4819_, v___x_4824_);
v_i_4819_ = v___x_4825_;
v_b_4821_ = v___y_4823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4853_, lean_object* v_i_4854_, lean_object* v_stop_4855_, lean_object* v_b_4856_){
_start:
{
size_t v_i_boxed_4857_; size_t v_stop_boxed_4858_; lean_object* v_res_4859_; 
v_i_boxed_4857_ = lean_unbox_usize(v_i_4854_);
lean_dec(v_i_4854_);
v_stop_boxed_4858_ = lean_unbox_usize(v_stop_4855_);
lean_dec(v_stop_4855_);
v_res_4859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4853_, v_i_boxed_4857_, v_stop_boxed_4858_, v_b_4856_);
lean_dec_ref(v_as_4853_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4860_){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4861_ = lean_unsigned_to_nat(0u);
v___x_4862_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4863_ = lean_array_get_size(v_sa_4860_);
v___x_4864_ = lean_nat_dec_lt(v___x_4861_, v___x_4863_);
if (v___x_4864_ == 0)
{
return v___x_4862_;
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4866_; size_t v___x_4867_; size_t v___x_4868_; lean_object* v___x_4869_; lean_object* v_snd_4870_; 
v___x_4865_ = lean_box(v___x_4864_);
v___x_4866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
lean_ctor_set(v___x_4866_, 1, v___x_4862_);
v___x_4867_ = ((size_t)0ULL);
v___x_4868_ = lean_usize_of_nat(v___x_4863_);
v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4860_, v___x_4867_, v___x_4868_, v___x_4866_);
v_snd_4870_ = lean_ctor_get(v___x_4869_, 1);
lean_inc(v_snd_4870_);
lean_dec_ref(v___x_4869_);
return v_snd_4870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4871_);
lean_dec_ref(v_sa_4871_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4873_, lean_object* v_sa_4874_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4874_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4876_, lean_object* v_sa_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l_Lean_Syntax_SepArray_getElems(v_sep_4876_, v_sa_4877_);
lean_dec_ref(v_sa_4877_);
lean_dec_ref(v_sep_4876_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4879_){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; uint8_t v___x_4883_; 
v___x_4880_ = lean_unsigned_to_nat(0u);
v___x_4881_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4882_ = lean_array_get_size(v_sa_4879_);
v___x_4883_ = lean_nat_dec_lt(v___x_4880_, v___x_4882_);
if (v___x_4883_ == 0)
{
return v___x_4881_;
}
else
{
lean_object* v___x_4884_; lean_object* v___x_4885_; size_t v___x_4886_; size_t v___x_4887_; lean_object* v___x_4888_; lean_object* v_snd_4889_; 
v___x_4884_ = lean_box(v___x_4883_);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
lean_ctor_set(v___x_4885_, 1, v___x_4881_);
v___x_4886_ = ((size_t)0ULL);
v___x_4887_ = lean_usize_of_nat(v___x_4882_);
v___x_4888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4879_, v___x_4886_, v___x_4887_, v___x_4885_);
v_snd_4889_ = lean_ctor_get(v___x_4888_, 1);
lean_inc(v_snd_4889_);
lean_dec_ref(v___x_4888_);
return v_snd_4889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4890_);
lean_dec_ref(v_sa_4890_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4892_, lean_object* v_sep_4893_, lean_object* v_sa_4894_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4896_, lean_object* v_sep_4897_, lean_object* v_sa_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_Syntax_TSepArray_getElems(v_k_4896_, v_sep_4897_, v_sa_4898_);
lean_dec_ref(v_sa_4898_);
lean_dec_ref(v_sep_4897_);
lean_dec(v_k_4896_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4900_, lean_object* v_sa_4901_, lean_object* v_e_4902_){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; uint8_t v___x_4905_; 
v___x_4903_ = lean_array_get_size(v_sa_4901_);
v___x_4904_ = lean_unsigned_to_nat(0u);
v___x_4905_ = lean_nat_dec_eq(v___x_4903_, v___x_4904_);
if (v___x_4905_ == 0)
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4906_ = l_Lean_mkAtom(v_sep_4900_);
v___x_4907_ = lean_array_push(v_sa_4901_, v___x_4906_);
v___x_4908_ = lean_array_push(v___x_4907_, v_e_4902_);
return v___x_4908_;
}
else
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec_ref(v_sa_4901_);
lean_dec_ref(v_sep_4900_);
v___x_4909_ = lean_unsigned_to_nat(1u);
v___x_4910_ = lean_mk_empty_array_with_capacity(v___x_4909_);
v___x_4911_ = lean_array_push(v___x_4910_, v_e_4902_);
return v___x_4911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4912_, lean_object* v_sep_4913_, lean_object* v_sa_4914_, lean_object* v_e_4915_){
_start:
{
lean_object* v___x_4916_; 
v___x_4916_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4913_, v_sa_4914_, v_e_4915_);
return v___x_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4917_, lean_object* v_sep_4918_, lean_object* v_sa_4919_, lean_object* v_e_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l_Lean_Syntax_TSepArray_push(v_k_4917_, v_sep_4918_, v_sa_4919_, v_e_4920_);
lean_dec(v_k_4917_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4925_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4929_);
lean_dec_ref(v_sep_4929_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4934_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4936_, lean_object* v_k_4937_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4939_, lean_object* v_k_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4939_, v_k_4940_);
lean_dec_ref(v_k_4940_);
lean_dec(v_sep_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object* v_sep_4942_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___boxed), 2, 1);
lean_closure_set(v___x_4943_, 0, v_sep_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4944_, lean_object* v_sep_4945_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4946_, 0, v_k_4944_);
lean_closure_set(v___x_4946_, 1, v_sep_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4947_, lean_object* v_x_4948_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_apply_1(v_inst_4947_, v_x_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v___x_4952_; size_t v_sz_4953_; size_t v___x_4954_; lean_object* v___x_4955_; 
v___x_4952_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4953_ = lean_array_size(v_a_4951_);
v___x_4954_ = ((size_t)0ULL);
v___x_4955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4952_, v___f_4950_, v_sz_4953_, v___x_4954_, v_a_4951_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_4956_){
_start:
{
lean_object* v___f_4957_; lean_object* v___f_4958_; 
v___f_4957_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4957_, 0, v_inst_4956_);
v___f_4958_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4958_, 0, v___f_4957_);
return v___f_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_4959_, lean_object* v_k_x27_4960_, lean_object* v_inst_4961_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_4963_, lean_object* v_k_x27_4964_, lean_object* v_inst_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_4963_, v_k_x27_4964_, v_inst_4965_);
lean_dec(v_k_x27_4964_);
lean_dec(v_k_4963_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_4967_){
_start:
{
lean_inc_ref(v_a_4967_);
return v_a_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_4968_);
lean_dec_ref(v_a_4968_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_4972_; 
v___f_4972_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_4975_){
_start:
{
lean_object* v___f_4976_; 
v___f_4976_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_4977_);
lean_dec(v_k_4977_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_4986_){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4987_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_4988_ = lean_box(2);
v___x_4989_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_4990_ = lean_unsigned_to_nat(2u);
v___x_4991_ = lean_mk_empty_array_with_capacity(v___x_4990_);
v___x_4992_ = lean_array_push(v___x_4991_, v_id_4986_);
v___x_4993_ = lean_array_push(v___x_4992_, v___x_4989_);
v___x_4994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4988_);
lean_ctor_set(v___x_4994_, 1, v___x_4987_);
lean_ctor_set(v___x_4994_, 2, v___x_4993_);
return v___x_4994_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = 123;
v___x_4999_ = lean_box_uint32(v___x_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5000_, lean_object* v_i_5001_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_Syntax_decodeQuotedChar(v_s_5000_, v_i_5001_);
if (lean_obj_tag(v___x_5002_) == 0)
{
uint32_t v_c_5003_; uint32_t v___x_5004_; uint8_t v___x_5005_; 
v_c_5003_ = lean_string_utf8_get(v_s_5000_, v_i_5001_);
v___x_5004_ = 123;
v___x_5005_ = lean_uint32_dec_eq(v_c_5003_, v___x_5004_);
if (v___x_5005_ == 0)
{
return v___x_5002_;
}
else
{
lean_object* v_i_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v_i_5006_ = lean_string_utf8_next(v_s_5000_, v_i_5001_);
v___x_5007_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5007_);
lean_ctor_set(v___x_5008_, 1, v_i_5006_);
v___x_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5008_);
return v___x_5009_;
}
}
else
{
return v___x_5002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5010_, lean_object* v_i_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5010_, v_i_5011_);
lean_dec(v_i_5011_);
lean_dec_ref(v_s_5010_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5013_, lean_object* v_i_5014_, lean_object* v_acc_5015_){
_start:
{
uint32_t v_c_5016_; uint32_t v___x_5017_; uint8_t v___x_5018_; 
v_c_5016_ = lean_string_utf8_get(v_s_5013_, v_i_5014_);
v___x_5017_ = 34;
v___x_5018_ = lean_uint32_dec_eq(v_c_5016_, v___x_5017_);
if (v___x_5018_ == 0)
{
uint32_t v___x_5019_; uint8_t v___x_5020_; 
v___x_5019_ = 123;
v___x_5020_ = lean_uint32_dec_eq(v_c_5016_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v_i_5021_; uint8_t v___x_5022_; 
v_i_5021_ = lean_string_utf8_next(v_s_5013_, v_i_5014_);
lean_dec(v_i_5014_);
v___x_5022_ = lean_string_utf8_at_end(v_s_5013_, v_i_5021_);
if (v___x_5022_ == 0)
{
uint32_t v___x_5023_; uint8_t v___x_5024_; 
v___x_5023_ = 92;
v___x_5024_ = lean_uint32_dec_eq(v_c_5016_, v___x_5023_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; 
v___x_5025_ = lean_string_push(v_acc_5015_, v_c_5016_);
v_i_5014_ = v_i_5021_;
v_acc_5015_ = v___x_5025_;
goto _start;
}
else
{
lean_object* v___x_5027_; 
v___x_5027_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5013_, v_i_5021_);
if (lean_obj_tag(v___x_5027_) == 1)
{
lean_object* v_val_5028_; lean_object* v_fst_5029_; lean_object* v_snd_5030_; uint32_t v___x_5031_; lean_object* v___x_5032_; 
lean_dec(v_i_5021_);
v_val_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_val_5028_);
lean_dec_ref_known(v___x_5027_, 1);
v_fst_5029_ = lean_ctor_get(v_val_5028_, 0);
lean_inc(v_fst_5029_);
v_snd_5030_ = lean_ctor_get(v_val_5028_, 1);
lean_inc(v_snd_5030_);
lean_dec(v_val_5028_);
v___x_5031_ = lean_unbox_uint32(v_fst_5029_);
lean_dec(v_fst_5029_);
v___x_5032_ = lean_string_push(v_acc_5015_, v___x_5031_);
v_i_5014_ = v_snd_5030_;
v_acc_5015_ = v___x_5032_;
goto _start;
}
else
{
lean_object* v___x_5034_; 
lean_dec(v___x_5027_);
lean_inc_ref(v_s_5013_);
v___x_5034_ = l_Lean_Syntax_decodeStringGap(v_s_5013_, v_i_5021_);
lean_dec(v_i_5021_);
if (lean_obj_tag(v___x_5034_) == 1)
{
lean_object* v_val_5035_; 
v_val_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_val_5035_);
lean_dec_ref_known(v___x_5034_, 1);
v_i_5014_ = v_val_5035_;
goto _start;
}
else
{
lean_object* v___x_5037_; 
lean_dec(v___x_5034_);
lean_dec_ref(v_acc_5015_);
lean_dec_ref(v_s_5013_);
v___x_5037_ = lean_box(0);
return v___x_5037_;
}
}
}
}
else
{
lean_object* v___x_5038_; 
lean_dec(v_i_5021_);
lean_dec_ref(v_acc_5015_);
lean_dec_ref(v_s_5013_);
v___x_5038_ = lean_box(0);
return v___x_5038_;
}
}
else
{
lean_object* v___x_5039_; 
lean_dec(v_i_5014_);
lean_dec_ref(v_s_5013_);
v___x_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5039_, 0, v_acc_5015_);
return v___x_5039_;
}
}
else
{
lean_object* v___x_5040_; 
lean_dec(v_i_5014_);
lean_dec_ref(v_s_5013_);
v___x_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5040_, 0, v_acc_5015_);
return v___x_5040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5041_){
_start:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = lean_unsigned_to_nat(1u);
v___x_5043_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5044_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5041_, v___x_5042_, v___x_5043_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5048_){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___x_5049_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5050_ = l_Lean_Syntax_isLit_x3f(v___x_5049_, v_stx_5048_);
if (lean_obj_tag(v___x_5050_) == 0)
{
return v___x_5050_;
}
else
{
lean_object* v_val_5051_; lean_object* v___x_5052_; 
v_val_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_val_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v___x_5052_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5051_);
return v___x_5052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5053_);
lean_dec(v_stx_5053_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5055_){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; uint8_t v___x_5060_; 
v___x_5056_ = l_Lean_Syntax_getArgs(v_stx_5055_);
v___x_5057_ = lean_unsigned_to_nat(0u);
v___x_5058_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5059_ = lean_array_get_size(v___x_5056_);
v___x_5060_ = lean_nat_dec_lt(v___x_5057_, v___x_5059_);
if (v___x_5060_ == 0)
{
lean_dec_ref(v___x_5056_);
return v___x_5058_;
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; size_t v___x_5063_; size_t v___x_5064_; lean_object* v___x_5065_; lean_object* v_snd_5066_; 
v___x_5061_ = lean_box(v___x_5060_);
v___x_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
lean_ctor_set(v___x_5062_, 1, v___x_5058_);
v___x_5063_ = ((size_t)0ULL);
v___x_5064_ = lean_usize_of_nat(v___x_5059_);
v___x_5065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5056_, v___x_5063_, v___x_5064_, v___x_5062_);
lean_dec_ref(v___x_5056_);
v_snd_5066_ = lean_ctor_get(v___x_5065_, 1);
lean_inc(v_snd_5066_);
lean_dec_ref(v___x_5065_);
return v_snd_5066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_Syntax_getSepArgs(v_stx_5067_);
lean_dec(v_stx_5067_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5069_, lean_object* v_mkElem_5070_, lean_object* v_mkLit_5071_, lean_object* v_as_5072_, size_t v_sz_5073_, size_t v_i_5074_, lean_object* v_b_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_a_5079_; lean_object* v_a_5080_; lean_object* v_elem_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; uint8_t v___x_5092_; 
v___x_5092_ = lean_usize_dec_lt(v_i_5074_, v_sz_5073_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; 
lean_dec_ref(v_mkLit_5071_);
lean_dec_ref(v_mkElem_5070_);
lean_dec_ref(v_mkAppend_5069_);
v___x_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5093_, 0, v_b_5075_);
lean_ctor_set(v___x_5093_, 1, v___y_5077_);
return v___x_5093_;
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5095_; 
v_a_5094_ = lean_array_uget_borrowed(v_as_5072_, v_i_5074_);
v___x_5095_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5094_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v_methods_5096_; lean_object* v_quotContext_5097_; lean_object* v_currMacroScope_5098_; lean_object* v_currRecDepth_5099_; lean_object* v_maxRecDepth_5100_; lean_object* v_ref_5101_; lean_object* v_ref_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v_methods_5096_ = lean_ctor_get(v___y_5076_, 0);
v_quotContext_5097_ = lean_ctor_get(v___y_5076_, 1);
v_currMacroScope_5098_ = lean_ctor_get(v___y_5076_, 2);
v_currRecDepth_5099_ = lean_ctor_get(v___y_5076_, 3);
v_maxRecDepth_5100_ = lean_ctor_get(v___y_5076_, 4);
v_ref_5101_ = lean_ctor_get(v___y_5076_, 5);
v_ref_5102_ = l_Lean_replaceRef(v_a_5094_, v_ref_5101_);
lean_inc(v_maxRecDepth_5100_);
lean_inc(v_currRecDepth_5099_);
lean_inc(v_currMacroScope_5098_);
lean_inc(v_quotContext_5097_);
lean_inc(v_methods_5096_);
v___x_5103_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5103_, 0, v_methods_5096_);
lean_ctor_set(v___x_5103_, 1, v_quotContext_5097_);
lean_ctor_set(v___x_5103_, 2, v_currMacroScope_5098_);
lean_ctor_set(v___x_5103_, 3, v_currRecDepth_5099_);
lean_ctor_set(v___x_5103_, 4, v_maxRecDepth_5100_);
lean_ctor_set(v___x_5103_, 5, v_ref_5102_);
lean_inc_ref(v_mkElem_5070_);
lean_inc(v_a_5094_);
v___x_5104_ = lean_apply_3(v_mkElem_5070_, v_a_5094_, v___x_5103_, v___y_5077_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v_a_5106_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5105_);
v_a_5106_ = lean_ctor_get(v___x_5104_, 1);
lean_inc(v_a_5106_);
lean_dec_ref_known(v___x_5104_, 2);
v_elem_5085_ = v_a_5105_;
v___y_5086_ = v___y_5076_;
v___y_5087_ = v_a_5106_;
goto v___jp_5084_;
}
else
{
lean_dec(v_b_5075_);
lean_dec_ref(v_mkLit_5071_);
lean_dec_ref(v_mkElem_5070_);
lean_dec_ref(v_mkAppend_5069_);
return v___x_5104_;
}
}
else
{
lean_object* v_val_5107_; uint8_t v___x_5108_; 
v_val_5107_ = lean_ctor_get(v___x_5095_, 0);
lean_inc_n(v_val_5107_, 2);
lean_dec_ref_known(v___x_5095_, 1);
v___x_5108_ = lean_string_isempty(v_val_5107_);
if (v___x_5108_ == 0)
{
lean_object* v_methods_5109_; lean_object* v_quotContext_5110_; lean_object* v_currMacroScope_5111_; lean_object* v_currRecDepth_5112_; lean_object* v_maxRecDepth_5113_; lean_object* v_ref_5114_; lean_object* v_ref_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
v_methods_5109_ = lean_ctor_get(v___y_5076_, 0);
v_quotContext_5110_ = lean_ctor_get(v___y_5076_, 1);
v_currMacroScope_5111_ = lean_ctor_get(v___y_5076_, 2);
v_currRecDepth_5112_ = lean_ctor_get(v___y_5076_, 3);
v_maxRecDepth_5113_ = lean_ctor_get(v___y_5076_, 4);
v_ref_5114_ = lean_ctor_get(v___y_5076_, 5);
v_ref_5115_ = l_Lean_replaceRef(v_a_5094_, v_ref_5114_);
lean_inc(v_maxRecDepth_5113_);
lean_inc(v_currRecDepth_5112_);
lean_inc(v_currMacroScope_5111_);
lean_inc(v_quotContext_5110_);
lean_inc(v_methods_5109_);
v___x_5116_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5116_, 0, v_methods_5109_);
lean_ctor_set(v___x_5116_, 1, v_quotContext_5110_);
lean_ctor_set(v___x_5116_, 2, v_currMacroScope_5111_);
lean_ctor_set(v___x_5116_, 3, v_currRecDepth_5112_);
lean_ctor_set(v___x_5116_, 4, v_maxRecDepth_5113_);
lean_ctor_set(v___x_5116_, 5, v_ref_5115_);
lean_inc_ref(v_mkLit_5071_);
v___x_5117_ = lean_apply_3(v_mkLit_5071_, v_val_5107_, v___x_5116_, v___y_5077_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v_a_5119_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
v_a_5119_ = lean_ctor_get(v___x_5117_, 1);
lean_inc(v_a_5119_);
lean_dec_ref_known(v___x_5117_, 2);
v_elem_5085_ = v_a_5118_;
v___y_5086_ = v___y_5076_;
v___y_5087_ = v_a_5119_;
goto v___jp_5084_;
}
else
{
lean_dec(v_b_5075_);
lean_dec_ref(v_mkLit_5071_);
lean_dec_ref(v_mkElem_5070_);
lean_dec_ref(v_mkAppend_5069_);
return v___x_5117_;
}
}
else
{
lean_dec(v_val_5107_);
v_a_5079_ = v_b_5075_;
v_a_5080_ = v___y_5077_;
goto v___jp_5078_;
}
}
}
v___jp_5078_:
{
size_t v___x_5081_; size_t v___x_5082_; 
v___x_5081_ = ((size_t)1ULL);
v___x_5082_ = lean_usize_add(v_i_5074_, v___x_5081_);
v_i_5074_ = v___x_5082_;
v_b_5075_ = v_a_5079_;
v___y_5077_ = v_a_5080_;
goto _start;
}
v___jp_5084_:
{
uint8_t v___x_5088_; 
v___x_5088_ = l_Lean_Syntax_isMissing(v_b_5075_);
if (v___x_5088_ == 0)
{
lean_object* v___x_5089_; 
lean_inc_ref(v_mkAppend_5069_);
lean_inc_ref(v___y_5086_);
v___x_5089_ = lean_apply_4(v_mkAppend_5069_, v_b_5075_, v_elem_5085_, v___y_5086_, v___y_5087_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v_a_5090_; lean_object* v_a_5091_; 
v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc(v_a_5090_);
v_a_5091_ = lean_ctor_get(v___x_5089_, 1);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5089_, 2);
v_a_5079_ = v_a_5090_;
v_a_5080_ = v_a_5091_;
goto v___jp_5078_;
}
else
{
lean_dec_ref(v_mkLit_5071_);
lean_dec_ref(v_mkElem_5070_);
lean_dec_ref(v_mkAppend_5069_);
return v___x_5089_;
}
}
else
{
lean_dec(v_b_5075_);
v_a_5079_ = v_elem_5085_;
v_a_5080_ = v___y_5087_;
goto v___jp_5078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5120_, lean_object* v_mkElem_5121_, lean_object* v_mkLit_5122_, lean_object* v_as_5123_, lean_object* v_sz_5124_, lean_object* v_i_5125_, lean_object* v_b_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_){
_start:
{
size_t v_sz_boxed_5129_; size_t v_i_boxed_5130_; lean_object* v_res_5131_; 
v_sz_boxed_5129_ = lean_unbox_usize(v_sz_5124_);
lean_dec(v_sz_5124_);
v_i_boxed_5130_ = lean_unbox_usize(v_i_5125_);
lean_dec(v_i_5125_);
v_res_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5120_, v_mkElem_5121_, v_mkLit_5122_, v_as_5123_, v_sz_boxed_5129_, v_i_boxed_5130_, v_b_5126_, v___y_5127_, v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec_ref(v_as_5123_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5132_, lean_object* v_mkAppend_5133_, lean_object* v_mkElem_5134_, lean_object* v_mkLit_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_){
_start:
{
lean_object* v_result_5138_; size_t v_sz_5139_; size_t v___x_5140_; lean_object* v___x_5141_; 
v_result_5138_ = lean_box(0);
v_sz_5139_ = lean_array_size(v_chunks_5132_);
v___x_5140_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5135_);
v___x_5141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5133_, v_mkElem_5134_, v_mkLit_5135_, v_chunks_5132_, v_sz_5139_, v___x_5140_, v_result_5138_, v_a_5136_, v_a_5137_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v_a_5143_; uint8_t v___x_5144_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5142_);
v_a_5143_ = lean_ctor_get(v___x_5141_, 1);
lean_inc(v_a_5143_);
v___x_5144_ = l_Lean_Syntax_isMissing(v_a_5142_);
lean_dec(v_a_5142_);
if (v___x_5144_ == 0)
{
lean_dec(v_a_5143_);
lean_dec_ref(v_mkLit_5135_);
return v___x_5141_;
}
else
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
lean_dec_ref_known(v___x_5141_, 2);
v___x_5145_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5136_);
v___x_5146_ = lean_apply_3(v_mkLit_5135_, v___x_5145_, v_a_5136_, v_a_5143_);
return v___x_5146_;
}
}
else
{
lean_dec_ref(v_mkLit_5135_);
return v___x_5141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5147_, lean_object* v_mkAppend_5148_, lean_object* v_mkElem_5149_, lean_object* v_mkLit_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5147_, v_mkAppend_5148_, v_mkElem_5149_, v_mkLit_5150_, v_a_5151_, v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec_ref(v_chunks_5147_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5158_, lean_object* v_b_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v_ref_5162_; uint8_t v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v_ref_5162_ = lean_ctor_get(v___y_5160_, 5);
v___x_5163_ = 0;
v___x_5164_ = l_Lean_SourceInfo_fromRef(v_ref_5162_, v___x_5163_);
v___x_5165_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5166_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5164_);
v___x_5167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5164_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
v___x_5168_ = l_Lean_Syntax_node3(v___x_5164_, v___x_5165_, v_a_5158_, v___x_5167_, v_b_5159_);
v___x_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5168_);
lean_ctor_set(v___x_5169_, 1, v___y_5161_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5170_, lean_object* v_b_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5170_, v_b_5171_, v___y_5172_, v___y_5173_);
lean_dec_ref(v___y_5172_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5175_, lean_object* v_a_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v_ref_5179_; uint8_t v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
v_ref_5179_ = lean_ctor_get(v___y_5177_, 5);
v___x_5180_ = 0;
v___x_5181_ = l_Lean_SourceInfo_fromRef(v_ref_5179_, v___x_5180_);
v___x_5182_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5183_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5181_);
v___x_5184_ = l_Lean_Syntax_node1(v___x_5181_, v___x_5183_, v_a_5176_);
v___x_5185_ = l_Lean_Syntax_node2(v___x_5181_, v___x_5182_, v_ofInterpFn_5175_, v___x_5184_);
v___x_5186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5185_);
lean_ctor_set(v___x_5186_, 1, v___y_5178_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5187_, lean_object* v_a_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5187_, v_a_5188_, v___y_5189_, v___y_5190_);
lean_dec_ref(v___y_5189_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5192_, lean_object* v_s_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_){
_start:
{
lean_object* v_ref_5196_; uint8_t v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v_ref_5196_ = lean_ctor_get(v___y_5194_, 5);
v___x_5197_ = 0;
v___x_5198_ = l_Lean_SourceInfo_fromRef(v_ref_5196_, v___x_5197_);
v___x_5199_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5200_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5201_ = lean_box(2);
v___x_5202_ = l_Lean_Syntax_mkStrLit(v_s_5193_, v___x_5201_);
lean_inc(v___x_5198_);
v___x_5203_ = l_Lean_Syntax_node1(v___x_5198_, v___x_5200_, v___x_5202_);
v___x_5204_ = l_Lean_Syntax_node2(v___x_5198_, v___x_5199_, v_ofLitFn_5192_, v___x_5203_);
v___x_5205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5204_);
lean_ctor_set(v___x_5205_, 1, v___y_5195_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5206_, lean_object* v_s_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5206_, v_s_5207_, v___y_5208_, v___y_5209_);
lean_dec_ref(v___y_5208_);
return v_res_5210_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5228_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5229_ = l_String_toRawSubstring_x27(v___x_5228_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5250_, lean_object* v_type_5251_, lean_object* v_ofInterpFn_5252_, lean_object* v_ofLitFn_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v___f_5256_; lean_object* v___f_5257_; lean_object* v___f_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___f_5256_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5257_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5257_, 0, v_ofInterpFn_5252_);
v___f_5258_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5258_, 0, v_ofLitFn_5253_);
v___x_5259_ = l_Lean_Syntax_getArgs(v_interpStr_5250_);
v___x_5260_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5259_, v___f_5256_, v___f_5257_, v___f_5258_, v_a_5254_, v_a_5255_);
lean_dec_ref(v___x_5259_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5293_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
v_a_5262_ = lean_ctor_get(v___x_5260_, 1);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5264_ = v___x_5260_;
v_isShared_5265_ = v_isSharedCheck_5293_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_inc(v_a_5261_);
lean_dec(v___x_5260_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5293_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v_quotContext_5266_; lean_object* v_currMacroScope_5267_; lean_object* v_ref_5268_; uint8_t v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5291_; 
v_quotContext_5266_ = lean_ctor_get(v_a_5254_, 1);
v_currMacroScope_5267_ = lean_ctor_get(v_a_5254_, 2);
v_ref_5268_ = lean_ctor_get(v_a_5254_, 5);
v___x_5269_ = 0;
v___x_5270_ = l_Lean_SourceInfo_fromRef(v_ref_5268_, v___x_5269_);
v___x_5271_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5272_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5273_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5270_, 7);
v___x_5274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5270_);
lean_ctor_set(v___x_5274_, 1, v___x_5273_);
v___x_5275_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5276_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5277_ = lean_box(0);
lean_inc(v_currMacroScope_5267_);
lean_inc(v_quotContext_5266_);
v___x_5278_ = l_Lean_addMacroScope(v_quotContext_5266_, v___x_5277_, v_currMacroScope_5267_);
v___x_5279_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5280_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5270_);
lean_ctor_set(v___x_5280_, 1, v___x_5276_);
lean_ctor_set(v___x_5280_, 2, v___x_5278_);
lean_ctor_set(v___x_5280_, 3, v___x_5279_);
v___x_5281_ = l_Lean_Syntax_node1(v___x_5270_, v___x_5275_, v___x_5280_);
v___x_5282_ = l_Lean_Syntax_node2(v___x_5270_, v___x_5272_, v___x_5274_, v___x_5281_);
v___x_5283_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5270_);
lean_ctor_set(v___x_5284_, 1, v___x_5283_);
v___x_5285_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5286_ = l_Lean_Syntax_node1(v___x_5270_, v___x_5285_, v_type_5251_);
v___x_5287_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5270_);
lean_ctor_set(v___x_5288_, 1, v___x_5287_);
v___x_5289_ = l_Lean_Syntax_node5(v___x_5270_, v___x_5271_, v___x_5282_, v_a_5261_, v___x_5284_, v___x_5286_, v___x_5288_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 0, v___x_5289_);
v___x_5291_ = v___x_5264_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
lean_ctor_set(v_reuseFailAlloc_5292_, 1, v_a_5262_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
else
{
lean_object* v_a_5294_; lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
lean_dec(v_type_5251_);
v_a_5294_ = lean_ctor_get(v___x_5260_, 0);
v_a_5295_ = lean_ctor_get(v___x_5260_, 1);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5260_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_inc(v_a_5294_);
lean_dec(v___x_5260_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5294_);
lean_ctor_set(v_reuseFailAlloc_5301_, 1, v_a_5295_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5303_, lean_object* v_type_5304_, lean_object* v_ofInterpFn_5305_, lean_object* v_ofLitFn_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5303_, v_type_5304_, v_ofInterpFn_5305_, v_ofLitFn_5306_, v_a_5307_, v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_interpStr_5303_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5310_){
_start:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5311_ = lean_unsigned_to_nat(1u);
v___x_5312_ = l_Lean_Syntax_getArg(v_stx_5310_, v___x_5311_);
if (lean_obj_tag(v___x_5312_) == 2)
{
lean_object* v_val_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v_val_5313_ = lean_ctor_get(v___x_5312_, 1);
lean_inc_ref(v_val_5313_);
lean_dec_ref_known(v___x_5312_, 2);
v___x_5314_ = lean_unsigned_to_nat(0u);
v___x_5315_ = lean_string_utf8_byte_size(v_val_5313_);
v___x_5316_ = lean_unsigned_to_nat(2u);
v___x_5317_ = lean_string_pos_sub(v___x_5315_, v___x_5316_);
v___x_5318_ = lean_string_utf8_extract(v_val_5313_, v___x_5314_, v___x_5317_);
lean_dec(v___x_5317_);
lean_dec_ref(v_val_5313_);
return v___x_5318_;
}
else
{
lean_object* v___x_5319_; 
lean_dec(v___x_5312_);
v___x_5319_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Lean_TSyntax_getDocString(v_stx_5320_);
lean_dec(v_stx_5320_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5340_, lean_object* v_prec_5341_){
_start:
{
lean_object* v___y_5343_; lean_object* v___y_5350_; lean_object* v___y_5357_; lean_object* v___y_5364_; lean_object* v___y_5371_; lean_object* v___y_5378_; 
switch(v_x_5340_)
{
case 0:
{
lean_object* v___x_5384_; uint8_t v___x_5385_; 
v___x_5384_ = lean_unsigned_to_nat(1024u);
v___x_5385_ = lean_nat_dec_le(v___x_5384_, v_prec_5341_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; 
v___x_5386_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5343_ = v___x_5386_;
goto v___jp_5342_;
}
else
{
lean_object* v___x_5387_; 
v___x_5387_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5343_ = v___x_5387_;
goto v___jp_5342_;
}
}
case 1:
{
lean_object* v___x_5388_; uint8_t v___x_5389_; 
v___x_5388_ = lean_unsigned_to_nat(1024u);
v___x_5389_ = lean_nat_dec_le(v___x_5388_, v_prec_5341_);
if (v___x_5389_ == 0)
{
lean_object* v___x_5390_; 
v___x_5390_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5350_ = v___x_5390_;
goto v___jp_5349_;
}
else
{
lean_object* v___x_5391_; 
v___x_5391_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5350_ = v___x_5391_;
goto v___jp_5349_;
}
}
case 2:
{
lean_object* v___x_5392_; uint8_t v___x_5393_; 
v___x_5392_ = lean_unsigned_to_nat(1024u);
v___x_5393_ = lean_nat_dec_le(v___x_5392_, v_prec_5341_);
if (v___x_5393_ == 0)
{
lean_object* v___x_5394_; 
v___x_5394_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5357_ = v___x_5394_;
goto v___jp_5356_;
}
else
{
lean_object* v___x_5395_; 
v___x_5395_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5357_ = v___x_5395_;
goto v___jp_5356_;
}
}
case 3:
{
lean_object* v___x_5396_; uint8_t v___x_5397_; 
v___x_5396_ = lean_unsigned_to_nat(1024u);
v___x_5397_ = lean_nat_dec_le(v___x_5396_, v_prec_5341_);
if (v___x_5397_ == 0)
{
lean_object* v___x_5398_; 
v___x_5398_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5364_ = v___x_5398_;
goto v___jp_5363_;
}
else
{
lean_object* v___x_5399_; 
v___x_5399_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5364_ = v___x_5399_;
goto v___jp_5363_;
}
}
case 4:
{
lean_object* v___x_5400_; uint8_t v___x_5401_; 
v___x_5400_ = lean_unsigned_to_nat(1024u);
v___x_5401_ = lean_nat_dec_le(v___x_5400_, v_prec_5341_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; 
v___x_5402_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5371_ = v___x_5402_;
goto v___jp_5370_;
}
else
{
lean_object* v___x_5403_; 
v___x_5403_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5371_ = v___x_5403_;
goto v___jp_5370_;
}
}
default: 
{
lean_object* v___x_5404_; uint8_t v___x_5405_; 
v___x_5404_ = lean_unsigned_to_nat(1024u);
v___x_5405_ = lean_nat_dec_le(v___x_5404_, v_prec_5341_);
if (v___x_5405_ == 0)
{
lean_object* v___x_5406_; 
v___x_5406_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5378_ = v___x_5406_;
goto v___jp_5377_;
}
else
{
lean_object* v___x_5407_; 
v___x_5407_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5378_ = v___x_5407_;
goto v___jp_5377_;
}
}
}
v___jp_5342_:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; uint8_t v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5344_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5343_);
v___x_5345_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5345_, 0, v___y_5343_);
lean_ctor_set(v___x_5345_, 1, v___x_5344_);
v___x_5346_ = 0;
v___x_5347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5347_, 0, v___x_5345_);
lean_ctor_set_uint8(v___x_5347_, sizeof(void*)*1, v___x_5346_);
v___x_5348_ = l_Repr_addAppParen(v___x_5347_, v_prec_5341_);
return v___x_5348_;
}
v___jp_5349_:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; uint8_t v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5351_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5350_);
v___x_5352_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5352_, 0, v___y_5350_);
lean_ctor_set(v___x_5352_, 1, v___x_5351_);
v___x_5353_ = 0;
v___x_5354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5354_, 0, v___x_5352_);
lean_ctor_set_uint8(v___x_5354_, sizeof(void*)*1, v___x_5353_);
v___x_5355_ = l_Repr_addAppParen(v___x_5354_, v_prec_5341_);
return v___x_5355_;
}
v___jp_5356_:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5358_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5357_);
v___x_5359_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5359_, 0, v___y_5357_);
lean_ctor_set(v___x_5359_, 1, v___x_5358_);
v___x_5360_ = 0;
v___x_5361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5361_, 0, v___x_5359_);
lean_ctor_set_uint8(v___x_5361_, sizeof(void*)*1, v___x_5360_);
v___x_5362_ = l_Repr_addAppParen(v___x_5361_, v_prec_5341_);
return v___x_5362_;
}
v___jp_5363_:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; uint8_t v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5365_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5364_);
v___x_5366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5366_, 0, v___y_5364_);
lean_ctor_set(v___x_5366_, 1, v___x_5365_);
v___x_5367_ = 0;
v___x_5368_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5368_, 0, v___x_5366_);
lean_ctor_set_uint8(v___x_5368_, sizeof(void*)*1, v___x_5367_);
v___x_5369_ = l_Repr_addAppParen(v___x_5368_, v_prec_5341_);
return v___x_5369_;
}
v___jp_5370_:
{
lean_object* v___x_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5372_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5371_);
v___x_5373_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5373_, 0, v___y_5371_);
lean_ctor_set(v___x_5373_, 1, v___x_5372_);
v___x_5374_ = 0;
v___x_5375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5375_, 0, v___x_5373_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*1, v___x_5374_);
v___x_5376_ = l_Repr_addAppParen(v___x_5375_, v_prec_5341_);
return v___x_5376_;
}
v___jp_5377_:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; uint8_t v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5379_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5378_);
v___x_5380_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5380_, 0, v___y_5378_);
lean_ctor_set(v___x_5380_, 1, v___x_5379_);
v___x_5381_ = 0;
v___x_5382_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5382_, 0, v___x_5380_);
lean_ctor_set_uint8(v___x_5382_, sizeof(void*)*1, v___x_5381_);
v___x_5383_ = l_Repr_addAppParen(v___x_5382_, v_prec_5341_);
return v___x_5383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5408_, lean_object* v_prec_5409_){
_start:
{
uint8_t v_x_329__boxed_5410_; lean_object* v_res_5411_; 
v_x_329__boxed_5410_ = lean_unbox(v_x_5408_);
v_res_5411_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5410_, v_prec_5409_);
lean_dec(v_prec_5409_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5423_, lean_object* v_prec_5424_){
_start:
{
lean_object* v___y_5426_; lean_object* v___y_5433_; lean_object* v___y_5440_; 
switch(v_x_5423_)
{
case 0:
{
lean_object* v___x_5446_; uint8_t v___x_5447_; 
v___x_5446_ = lean_unsigned_to_nat(1024u);
v___x_5447_ = lean_nat_dec_le(v___x_5446_, v_prec_5424_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; 
v___x_5448_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5426_ = v___x_5448_;
goto v___jp_5425_;
}
else
{
lean_object* v___x_5449_; 
v___x_5449_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5426_ = v___x_5449_;
goto v___jp_5425_;
}
}
case 1:
{
lean_object* v___x_5450_; uint8_t v___x_5451_; 
v___x_5450_ = lean_unsigned_to_nat(1024u);
v___x_5451_ = lean_nat_dec_le(v___x_5450_, v_prec_5424_);
if (v___x_5451_ == 0)
{
lean_object* v___x_5452_; 
v___x_5452_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5433_ = v___x_5452_;
goto v___jp_5432_;
}
else
{
lean_object* v___x_5453_; 
v___x_5453_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5433_ = v___x_5453_;
goto v___jp_5432_;
}
}
default: 
{
lean_object* v___x_5454_; uint8_t v___x_5455_; 
v___x_5454_ = lean_unsigned_to_nat(1024u);
v___x_5455_ = lean_nat_dec_le(v___x_5454_, v_prec_5424_);
if (v___x_5455_ == 0)
{
lean_object* v___x_5456_; 
v___x_5456_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5440_ = v___x_5456_;
goto v___jp_5439_;
}
else
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5440_ = v___x_5457_;
goto v___jp_5439_;
}
}
}
v___jp_5425_:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5427_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5426_);
v___x_5428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___y_5426_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = 0;
v___x_5430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5430_, 0, v___x_5428_);
lean_ctor_set_uint8(v___x_5430_, sizeof(void*)*1, v___x_5429_);
v___x_5431_ = l_Repr_addAppParen(v___x_5430_, v_prec_5424_);
return v___x_5431_;
}
v___jp_5432_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; uint8_t v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5434_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5433_);
v___x_5435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___y_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = 0;
v___x_5437_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5437_, 0, v___x_5435_);
lean_ctor_set_uint8(v___x_5437_, sizeof(void*)*1, v___x_5436_);
v___x_5438_ = l_Repr_addAppParen(v___x_5437_, v_prec_5424_);
return v___x_5438_;
}
v___jp_5439_:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; uint8_t v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v___x_5441_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5440_);
v___x_5442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5442_, 0, v___y_5440_);
lean_ctor_set(v___x_5442_, 1, v___x_5441_);
v___x_5443_ = 0;
v___x_5444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5444_, 0, v___x_5442_);
lean_ctor_set_uint8(v___x_5444_, sizeof(void*)*1, v___x_5443_);
v___x_5445_ = l_Repr_addAppParen(v___x_5444_, v_prec_5424_);
return v___x_5445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5458_, lean_object* v_prec_5459_){
_start:
{
uint8_t v_x_167__boxed_5460_; lean_object* v_res_5461_; 
v_x_167__boxed_5460_ = lean_unbox(v_x_5458_);
v_res_5461_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5460_, v_prec_5459_);
lean_dec(v_prec_5459_);
return v_res_5461_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = lean_unsigned_to_nat(8u);
v___x_5474_ = lean_nat_to_int(v___x_5473_);
return v___x_5474_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5484_ = lean_unsigned_to_nat(13u);
v___x_5485_ = lean_nat_to_int(v___x_5484_);
return v___x_5485_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; 
v___x_5495_ = lean_unsigned_to_nat(10u);
v___x_5496_ = lean_nat_to_int(v___x_5495_);
return v___x_5496_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; 
v___x_5500_ = lean_unsigned_to_nat(14u);
v___x_5501_ = lean_nat_to_int(v___x_5500_);
return v___x_5501_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5505_ = lean_unsigned_to_nat(19u);
v___x_5506_ = lean_nat_to_int(v___x_5505_);
return v___x_5506_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = lean_unsigned_to_nat(20u);
v___x_5511_ = lean_nat_to_int(v___x_5510_);
return v___x_5511_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5518_ = lean_unsigned_to_nat(9u);
v___x_5519_ = lean_nat_to_int(v___x_5518_);
return v___x_5519_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5526_ = lean_unsigned_to_nat(12u);
v___x_5527_ = lean_nat_to_int(v___x_5526_);
return v___x_5527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5534_){
_start:
{
uint8_t v_zeta_5535_; uint8_t v_beta_5536_; uint8_t v_eta_5537_; uint8_t v_etaStruct_5538_; uint8_t v_iota_5539_; uint8_t v_proj_5540_; uint8_t v_decide_5541_; uint8_t v_autoUnfold_5542_; uint8_t v_failIfUnchanged_5543_; uint8_t v_unfoldPartialApp_5544_; uint8_t v_zetaDelta_5545_; uint8_t v_index_5546_; uint8_t v_zetaUnused_5547_; uint8_t v_zetaHave_5548_; uint8_t v_locals_5549_; uint8_t v_instances_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; uint8_t v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; 
v_zeta_5535_ = lean_ctor_get_uint8(v_x_5534_, 0);
v_beta_5536_ = lean_ctor_get_uint8(v_x_5534_, 1);
v_eta_5537_ = lean_ctor_get_uint8(v_x_5534_, 2);
v_etaStruct_5538_ = lean_ctor_get_uint8(v_x_5534_, 3);
v_iota_5539_ = lean_ctor_get_uint8(v_x_5534_, 4);
v_proj_5540_ = lean_ctor_get_uint8(v_x_5534_, 5);
v_decide_5541_ = lean_ctor_get_uint8(v_x_5534_, 6);
v_autoUnfold_5542_ = lean_ctor_get_uint8(v_x_5534_, 7);
v_failIfUnchanged_5543_ = lean_ctor_get_uint8(v_x_5534_, 8);
v_unfoldPartialApp_5544_ = lean_ctor_get_uint8(v_x_5534_, 9);
v_zetaDelta_5545_ = lean_ctor_get_uint8(v_x_5534_, 10);
v_index_5546_ = lean_ctor_get_uint8(v_x_5534_, 11);
v_zetaUnused_5547_ = lean_ctor_get_uint8(v_x_5534_, 12);
v_zetaHave_5548_ = lean_ctor_get_uint8(v_x_5534_, 13);
v_locals_5549_ = lean_ctor_get_uint8(v_x_5534_, 14);
v_instances_5550_ = lean_ctor_get_uint8(v_x_5534_, 15);
v___x_5551_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5552_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5553_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5554_ = lean_unsigned_to_nat(0u);
v___x_5555_ = l_Bool_repr___redArg(v_zeta_5535_);
v___x_5556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5556_, 0, v___x_5553_);
lean_ctor_set(v___x_5556_, 1, v___x_5555_);
v___x_5557_ = 0;
v___x_5558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5558_, 0, v___x_5556_);
lean_ctor_set_uint8(v___x_5558_, sizeof(void*)*1, v___x_5557_);
v___x_5559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5552_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
v___x_5560_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5561_, 0, v___x_5559_);
lean_ctor_set(v___x_5561_, 1, v___x_5560_);
v___x_5562_ = lean_box(1);
v___x_5563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5561_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
v___x_5564_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5563_);
lean_ctor_set(v___x_5565_, 1, v___x_5564_);
v___x_5566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5565_);
lean_ctor_set(v___x_5566_, 1, v___x_5551_);
v___x_5567_ = l_Bool_repr___redArg(v_beta_5536_);
v___x_5568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5553_);
lean_ctor_set(v___x_5568_, 1, v___x_5567_);
v___x_5569_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5569_, 0, v___x_5568_);
lean_ctor_set_uint8(v___x_5569_, sizeof(void*)*1, v___x_5557_);
v___x_5570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5566_);
lean_ctor_set(v___x_5570_, 1, v___x_5569_);
v___x_5571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5570_);
lean_ctor_set(v___x_5571_, 1, v___x_5560_);
v___x_5572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5572_, 0, v___x_5571_);
lean_ctor_set(v___x_5572_, 1, v___x_5562_);
v___x_5573_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5574_, 0, v___x_5572_);
lean_ctor_set(v___x_5574_, 1, v___x_5573_);
v___x_5575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5574_);
lean_ctor_set(v___x_5575_, 1, v___x_5551_);
v___x_5576_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5577_ = l_Bool_repr___redArg(v_eta_5537_);
v___x_5578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5578_, 0, v___x_5576_);
lean_ctor_set(v___x_5578_, 1, v___x_5577_);
v___x_5579_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
lean_ctor_set_uint8(v___x_5579_, sizeof(void*)*1, v___x_5557_);
v___x_5580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5575_);
lean_ctor_set(v___x_5580_, 1, v___x_5579_);
v___x_5581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5581_, 0, v___x_5580_);
lean_ctor_set(v___x_5581_, 1, v___x_5560_);
v___x_5582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
lean_ctor_set(v___x_5582_, 1, v___x_5562_);
v___x_5583_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5582_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
lean_ctor_set(v___x_5585_, 1, v___x_5551_);
v___x_5586_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5587_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5538_, v___x_5554_);
v___x_5588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5586_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
v___x_5589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
lean_ctor_set_uint8(v___x_5589_, sizeof(void*)*1, v___x_5557_);
v___x_5590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5590_, 0, v___x_5585_);
lean_ctor_set(v___x_5590_, 1, v___x_5589_);
v___x_5591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5590_);
lean_ctor_set(v___x_5591_, 1, v___x_5560_);
v___x_5592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5591_);
lean_ctor_set(v___x_5592_, 1, v___x_5562_);
v___x_5593_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5594_, 0, v___x_5592_);
lean_ctor_set(v___x_5594_, 1, v___x_5593_);
v___x_5595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5594_);
lean_ctor_set(v___x_5595_, 1, v___x_5551_);
v___x_5596_ = l_Bool_repr___redArg(v_iota_5539_);
v___x_5597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5597_, 0, v___x_5553_);
lean_ctor_set(v___x_5597_, 1, v___x_5596_);
v___x_5598_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5598_, 0, v___x_5597_);
lean_ctor_set_uint8(v___x_5598_, sizeof(void*)*1, v___x_5557_);
v___x_5599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5595_);
lean_ctor_set(v___x_5599_, 1, v___x_5598_);
v___x_5600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5600_, 0, v___x_5599_);
lean_ctor_set(v___x_5600_, 1, v___x_5560_);
v___x_5601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5601_, 0, v___x_5600_);
lean_ctor_set(v___x_5601_, 1, v___x_5562_);
v___x_5602_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5603_, 0, v___x_5601_);
lean_ctor_set(v___x_5603_, 1, v___x_5602_);
v___x_5604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
lean_ctor_set(v___x_5604_, 1, v___x_5551_);
v___x_5605_ = l_Bool_repr___redArg(v_proj_5540_);
v___x_5606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5553_);
lean_ctor_set(v___x_5606_, 1, v___x_5605_);
v___x_5607_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5607_, 0, v___x_5606_);
lean_ctor_set_uint8(v___x_5607_, sizeof(void*)*1, v___x_5557_);
v___x_5608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5608_, 0, v___x_5604_);
lean_ctor_set(v___x_5608_, 1, v___x_5607_);
v___x_5609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5608_);
lean_ctor_set(v___x_5609_, 1, v___x_5560_);
v___x_5610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
lean_ctor_set(v___x_5610_, 1, v___x_5562_);
v___x_5611_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5610_);
lean_ctor_set(v___x_5612_, 1, v___x_5611_);
v___x_5613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5612_);
lean_ctor_set(v___x_5613_, 1, v___x_5551_);
v___x_5614_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5615_ = l_Bool_repr___redArg(v_decide_5541_);
v___x_5616_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5614_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5617_, 0, v___x_5616_);
lean_ctor_set_uint8(v___x_5617_, sizeof(void*)*1, v___x_5557_);
v___x_5618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5613_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
lean_ctor_set(v___x_5619_, 1, v___x_5560_);
v___x_5620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5619_);
lean_ctor_set(v___x_5620_, 1, v___x_5562_);
v___x_5621_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5620_);
lean_ctor_set(v___x_5622_, 1, v___x_5621_);
v___x_5623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set(v___x_5623_, 1, v___x_5551_);
v___x_5624_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5625_ = l_Bool_repr___redArg(v_autoUnfold_5542_);
v___x_5626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5624_);
lean_ctor_set(v___x_5626_, 1, v___x_5625_);
v___x_5627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set_uint8(v___x_5627_, sizeof(void*)*1, v___x_5557_);
v___x_5628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5623_);
lean_ctor_set(v___x_5628_, 1, v___x_5627_);
v___x_5629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5628_);
lean_ctor_set(v___x_5629_, 1, v___x_5560_);
v___x_5630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5629_);
lean_ctor_set(v___x_5630_, 1, v___x_5562_);
v___x_5631_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5630_);
lean_ctor_set(v___x_5632_, 1, v___x_5631_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v___x_5551_);
v___x_5634_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5635_ = l_Bool_repr___redArg(v_failIfUnchanged_5543_);
v___x_5636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set(v___x_5636_, 1, v___x_5635_);
v___x_5637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set_uint8(v___x_5637_, sizeof(void*)*1, v___x_5557_);
v___x_5638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5633_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
lean_ctor_set(v___x_5639_, 1, v___x_5560_);
v___x_5640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5639_);
lean_ctor_set(v___x_5640_, 1, v___x_5562_);
v___x_5641_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5640_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
lean_ctor_set(v___x_5643_, 1, v___x_5551_);
v___x_5644_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5645_ = l_Bool_repr___redArg(v_unfoldPartialApp_5544_);
v___x_5646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5644_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
v___x_5647_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set_uint8(v___x_5647_, sizeof(void*)*1, v___x_5557_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5643_);
lean_ctor_set(v___x_5648_, 1, v___x_5647_);
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5648_);
lean_ctor_set(v___x_5649_, 1, v___x_5560_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set(v___x_5650_, 1, v___x_5562_);
v___x_5651_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5650_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5551_);
v___x_5654_ = l_Bool_repr___redArg(v_zetaDelta_5545_);
v___x_5655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5586_);
lean_ctor_set(v___x_5655_, 1, v___x_5654_);
v___x_5656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5656_, 0, v___x_5655_);
lean_ctor_set_uint8(v___x_5656_, sizeof(void*)*1, v___x_5557_);
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5653_);
lean_ctor_set(v___x_5657_, 1, v___x_5656_);
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
lean_ctor_set(v___x_5658_, 1, v___x_5560_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set(v___x_5659_, 1, v___x_5562_);
v___x_5660_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5659_);
lean_ctor_set(v___x_5661_, 1, v___x_5660_);
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
lean_ctor_set(v___x_5662_, 1, v___x_5551_);
v___x_5663_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5664_ = l_Bool_repr___redArg(v_index_5546_);
v___x_5665_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5663_);
lean_ctor_set(v___x_5665_, 1, v___x_5664_);
v___x_5666_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
lean_ctor_set_uint8(v___x_5666_, sizeof(void*)*1, v___x_5557_);
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5662_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___x_5560_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set(v___x_5669_, 1, v___x_5562_);
v___x_5670_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5669_);
lean_ctor_set(v___x_5671_, 1, v___x_5670_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
lean_ctor_set(v___x_5672_, 1, v___x_5551_);
v___x_5673_ = l_Bool_repr___redArg(v_zetaUnused_5547_);
v___x_5674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5624_);
lean_ctor_set(v___x_5674_, 1, v___x_5673_);
v___x_5675_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set_uint8(v___x_5675_, sizeof(void*)*1, v___x_5557_);
v___x_5676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5672_);
lean_ctor_set(v___x_5676_, 1, v___x_5675_);
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5676_);
lean_ctor_set(v___x_5677_, 1, v___x_5560_);
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set(v___x_5678_, 1, v___x_5562_);
v___x_5679_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5678_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5680_);
lean_ctor_set(v___x_5681_, 1, v___x_5551_);
v___x_5682_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5683_ = l_Bool_repr___redArg(v_zetaHave_5548_);
v___x_5684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5682_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set_uint8(v___x_5685_, sizeof(void*)*1, v___x_5557_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5681_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5686_);
lean_ctor_set(v___x_5687_, 1, v___x_5560_);
v___x_5688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set(v___x_5688_, 1, v___x_5562_);
v___x_5689_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5688_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5551_);
v___x_5692_ = l_Bool_repr___redArg(v_locals_5549_);
v___x_5693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5614_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
v___x_5694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
lean_ctor_set_uint8(v___x_5694_, sizeof(void*)*1, v___x_5557_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5691_);
lean_ctor_set(v___x_5695_, 1, v___x_5694_);
v___x_5696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5695_);
lean_ctor_set(v___x_5696_, 1, v___x_5560_);
v___x_5697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
lean_ctor_set(v___x_5697_, 1, v___x_5562_);
v___x_5698_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5697_);
lean_ctor_set(v___x_5699_, 1, v___x_5698_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set(v___x_5700_, 1, v___x_5551_);
v___x_5701_ = l_Bool_repr___redArg(v_instances_5550_);
v___x_5702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5586_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*1, v___x_5557_);
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5700_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5706_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
lean_ctor_set(v___x_5707_, 1, v___x_5704_);
v___x_5708_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5707_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5705_);
lean_ctor_set(v___x_5710_, 1, v___x_5709_);
v___x_5711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set_uint8(v___x_5711_, sizeof(void*)*1, v___x_5557_);
return v___x_5711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5712_);
lean_dec_ref(v_x_5712_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5714_, lean_object* v_prec_5715_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5714_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5717_, lean_object* v_prec_5718_){
_start:
{
lean_object* v_res_5719_; 
v_res_5719_ = l_Lean_Meta_instReprConfig_repr(v_x_5717_, v_prec_5718_);
lean_dec(v_prec_5718_);
lean_dec_ref(v_x_5717_);
return v_res_5719_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5727_, lean_object* v_x_5728_){
_start:
{
if (lean_obj_tag(v_x_5727_) == 0)
{
lean_object* v___x_5729_; 
v___x_5729_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5729_;
}
else
{
lean_object* v_val_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5741_; 
v_val_5730_ = lean_ctor_get(v_x_5727_, 0);
v_isSharedCheck_5741_ = !lean_is_exclusive(v_x_5727_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5732_ = v_x_5727_;
v_isShared_5733_ = v_isSharedCheck_5741_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_val_5730_);
lean_dec(v_x_5727_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5741_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5737_; 
v___x_5734_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5735_ = l_Nat_reprFast(v_val_5730_);
if (v_isShared_5733_ == 0)
{
lean_ctor_set_tag(v___x_5732_, 3);
lean_ctor_set(v___x_5732_, 0, v___x_5735_);
v___x_5737_ = v___x_5732_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5735_);
v___x_5737_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
lean_object* v___x_5738_; lean_object* v___x_5739_; 
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5734_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = l_Repr_addAppParen(v___x_5738_, v_x_5728_);
return v___x_5739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5742_, lean_object* v_x_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5742_, v_x_5743_);
lean_dec(v_x_5743_);
return v_res_5744_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5757_ = lean_unsigned_to_nat(21u);
v___x_5758_ = lean_nat_to_int(v___x_5757_);
return v___x_5758_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5765_; lean_object* v___x_5766_; 
v___x_5765_ = lean_unsigned_to_nat(11u);
v___x_5766_ = lean_nat_to_int(v___x_5765_);
return v___x_5766_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5782_ = lean_unsigned_to_nat(23u);
v___x_5783_ = lean_nat_to_int(v___x_5782_);
return v___x_5783_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; 
v___x_5787_ = lean_unsigned_to_nat(16u);
v___x_5788_ = lean_nat_to_int(v___x_5787_);
return v___x_5788_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5795_; lean_object* v___x_5796_; 
v___x_5795_ = lean_unsigned_to_nat(15u);
v___x_5796_ = lean_nat_to_int(v___x_5795_);
return v___x_5796_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5803_; lean_object* v___x_5804_; 
v___x_5803_ = lean_unsigned_to_nat(17u);
v___x_5804_ = lean_nat_to_int(v___x_5803_);
return v___x_5804_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5811_ = lean_unsigned_to_nat(18u);
v___x_5812_ = lean_nat_to_int(v___x_5811_);
return v___x_5812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5813_){
_start:
{
lean_object* v_maxSteps_5814_; lean_object* v_maxDischargeDepth_5815_; uint8_t v_contextual_5816_; uint8_t v_memoize_5817_; uint8_t v_singlePass_5818_; uint8_t v_zeta_5819_; uint8_t v_beta_5820_; uint8_t v_eta_5821_; uint8_t v_etaStruct_5822_; uint8_t v_iota_5823_; uint8_t v_proj_5824_; uint8_t v_decide_5825_; uint8_t v_arith_5826_; uint8_t v_autoUnfold_5827_; uint8_t v_dsimp_5828_; uint8_t v_failIfUnchanged_5829_; uint8_t v_ground_5830_; uint8_t v_unfoldPartialApp_5831_; uint8_t v_zetaDelta_5832_; uint8_t v_index_5833_; uint8_t v_implicitDefEqProofs_5834_; uint8_t v_zetaUnused_5835_; uint8_t v_catchRuntime_5836_; uint8_t v_zetaHave_5837_; uint8_t v_letToHave_5838_; uint8_t v_congrConsts_5839_; uint8_t v_bitVecOfNat_5840_; uint8_t v_warnExponents_5841_; uint8_t v_suggestions_5842_; lean_object* v_maxSuggestions_5843_; uint8_t v_locals_5844_; uint8_t v_instances_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; uint8_t v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; 
v_maxSteps_5814_ = lean_ctor_get(v_x_5813_, 0);
lean_inc(v_maxSteps_5814_);
v_maxDischargeDepth_5815_ = lean_ctor_get(v_x_5813_, 1);
lean_inc(v_maxDischargeDepth_5815_);
v_contextual_5816_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3);
v_memoize_5817_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 1);
v_singlePass_5818_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 2);
v_zeta_5819_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 3);
v_beta_5820_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 4);
v_eta_5821_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 5);
v_etaStruct_5822_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 6);
v_iota_5823_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 7);
v_proj_5824_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 8);
v_decide_5825_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 9);
v_arith_5826_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 10);
v_autoUnfold_5827_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 11);
v_dsimp_5828_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5829_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 13);
v_ground_5830_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5831_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 15);
v_zetaDelta_5832_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 16);
v_index_5833_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5834_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 18);
v_zetaUnused_5835_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 19);
v_catchRuntime_5836_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 20);
v_zetaHave_5837_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 21);
v_letToHave_5838_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 22);
v_congrConsts_5839_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5840_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 24);
v_warnExponents_5841_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 25);
v_suggestions_5842_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 26);
v_maxSuggestions_5843_ = lean_ctor_get(v_x_5813_, 2);
lean_inc(v_maxSuggestions_5843_);
v_locals_5844_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 27);
v_instances_5845_ = lean_ctor_get_uint8(v_x_5813_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5813_);
v___x_5846_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5847_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5848_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5849_ = l_Nat_reprFast(v_maxSteps_5814_);
v___x_5850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5850_, 0, v___x_5849_);
v___x_5851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5848_);
lean_ctor_set(v___x_5851_, 1, v___x_5850_);
v___x_5852_ = 0;
v___x_5853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5853_, 0, v___x_5851_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*1, v___x_5852_);
v___x_5854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5847_);
lean_ctor_set(v___x_5854_, 1, v___x_5853_);
v___x_5855_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5854_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
v___x_5857_ = lean_box(1);
v___x_5858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5856_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5858_);
lean_ctor_set(v___x_5860_, 1, v___x_5859_);
v___x_5861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5860_);
lean_ctor_set(v___x_5861_, 1, v___x_5846_);
v___x_5862_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5863_ = l_Nat_reprFast(v_maxDischargeDepth_5815_);
v___x_5864_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5863_);
v___x_5865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5862_);
lean_ctor_set(v___x_5865_, 1, v___x_5864_);
v___x_5866_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5866_, 0, v___x_5865_);
lean_ctor_set_uint8(v___x_5866_, sizeof(void*)*1, v___x_5852_);
v___x_5867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5867_, 0, v___x_5861_);
lean_ctor_set(v___x_5867_, 1, v___x_5866_);
v___x_5868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5867_);
lean_ctor_set(v___x_5868_, 1, v___x_5855_);
v___x_5869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5868_);
lean_ctor_set(v___x_5869_, 1, v___x_5857_);
v___x_5870_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5869_);
lean_ctor_set(v___x_5871_, 1, v___x_5870_);
v___x_5872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
lean_ctor_set(v___x_5872_, 1, v___x_5846_);
v___x_5873_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5874_ = lean_unsigned_to_nat(0u);
v___x_5875_ = l_Bool_repr___redArg(v_contextual_5816_);
v___x_5876_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5873_);
lean_ctor_set(v___x_5876_, 1, v___x_5875_);
v___x_5877_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5877_, 0, v___x_5876_);
lean_ctor_set_uint8(v___x_5877_, sizeof(void*)*1, v___x_5852_);
v___x_5878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5872_);
lean_ctor_set(v___x_5878_, 1, v___x_5877_);
v___x_5879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5879_, 0, v___x_5878_);
lean_ctor_set(v___x_5879_, 1, v___x_5855_);
v___x_5880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5880_, 0, v___x_5879_);
lean_ctor_set(v___x_5880_, 1, v___x_5857_);
v___x_5881_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5880_);
lean_ctor_set(v___x_5882_, 1, v___x_5881_);
v___x_5883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5882_);
lean_ctor_set(v___x_5883_, 1, v___x_5846_);
v___x_5884_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5885_ = l_Bool_repr___redArg(v_memoize_5817_);
v___x_5886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5886_, 0, v___x_5884_);
lean_ctor_set(v___x_5886_, 1, v___x_5885_);
v___x_5887_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5887_, 0, v___x_5886_);
lean_ctor_set_uint8(v___x_5887_, sizeof(void*)*1, v___x_5852_);
v___x_5888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5883_);
lean_ctor_set(v___x_5888_, 1, v___x_5887_);
v___x_5889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5888_);
lean_ctor_set(v___x_5889_, 1, v___x_5855_);
v___x_5890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5889_);
lean_ctor_set(v___x_5890_, 1, v___x_5857_);
v___x_5891_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5890_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5892_);
lean_ctor_set(v___x_5893_, 1, v___x_5846_);
v___x_5894_ = l_Bool_repr___redArg(v_singlePass_5818_);
v___x_5895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5873_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5896_, 0, v___x_5895_);
lean_ctor_set_uint8(v___x_5896_, sizeof(void*)*1, v___x_5852_);
v___x_5897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5893_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
v___x_5898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5897_);
lean_ctor_set(v___x_5898_, 1, v___x_5855_);
v___x_5899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5898_);
lean_ctor_set(v___x_5899_, 1, v___x_5857_);
v___x_5900_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5899_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
v___x_5902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5901_);
lean_ctor_set(v___x_5902_, 1, v___x_5846_);
v___x_5903_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5904_ = l_Bool_repr___redArg(v_zeta_5819_);
v___x_5905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5903_);
lean_ctor_set(v___x_5905_, 1, v___x_5904_);
v___x_5906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5906_, 0, v___x_5905_);
lean_ctor_set_uint8(v___x_5906_, sizeof(void*)*1, v___x_5852_);
v___x_5907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5902_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5907_);
lean_ctor_set(v___x_5908_, 1, v___x_5855_);
v___x_5909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5908_);
lean_ctor_set(v___x_5909_, 1, v___x_5857_);
v___x_5910_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5909_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
lean_ctor_set(v___x_5912_, 1, v___x_5846_);
v___x_5913_ = l_Bool_repr___redArg(v_beta_5820_);
v___x_5914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5903_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v___x_5915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5915_, 0, v___x_5914_);
lean_ctor_set_uint8(v___x_5915_, sizeof(void*)*1, v___x_5852_);
v___x_5916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5912_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5916_);
lean_ctor_set(v___x_5917_, 1, v___x_5855_);
v___x_5918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
lean_ctor_set(v___x_5918_, 1, v___x_5857_);
v___x_5919_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5918_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5920_);
lean_ctor_set(v___x_5921_, 1, v___x_5846_);
v___x_5922_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5923_ = l_Bool_repr___redArg(v_eta_5821_);
v___x_5924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5922_);
lean_ctor_set(v___x_5924_, 1, v___x_5923_);
v___x_5925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5925_, 0, v___x_5924_);
lean_ctor_set_uint8(v___x_5925_, sizeof(void*)*1, v___x_5852_);
v___x_5926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5921_);
lean_ctor_set(v___x_5926_, 1, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5926_);
lean_ctor_set(v___x_5927_, 1, v___x_5855_);
v___x_5928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set(v___x_5928_, 1, v___x_5857_);
v___x_5929_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5928_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5846_);
v___x_5932_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5933_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5822_, v___x_5874_);
v___x_5934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set_uint8(v___x_5935_, sizeof(void*)*1, v___x_5852_);
v___x_5936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5931_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5936_);
lean_ctor_set(v___x_5937_, 1, v___x_5855_);
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
lean_ctor_set(v___x_5938_, 1, v___x_5857_);
v___x_5939_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5938_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5846_);
v___x_5942_ = l_Bool_repr___redArg(v_iota_5823_);
v___x_5943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5903_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
v___x_5944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
lean_ctor_set_uint8(v___x_5944_, sizeof(void*)*1, v___x_5852_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5941_);
lean_ctor_set(v___x_5945_, 1, v___x_5944_);
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
lean_ctor_set(v___x_5946_, 1, v___x_5855_);
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set(v___x_5947_, 1, v___x_5857_);
v___x_5948_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5947_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set(v___x_5950_, 1, v___x_5846_);
v___x_5951_ = l_Bool_repr___redArg(v_proj_5824_);
v___x_5952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5903_);
lean_ctor_set(v___x_5952_, 1, v___x_5951_);
v___x_5953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5953_, 0, v___x_5952_);
lean_ctor_set_uint8(v___x_5953_, sizeof(void*)*1, v___x_5852_);
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5950_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set(v___x_5955_, 1, v___x_5855_);
v___x_5956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5955_);
lean_ctor_set(v___x_5956_, 1, v___x_5857_);
v___x_5957_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5956_);
lean_ctor_set(v___x_5958_, 1, v___x_5957_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
lean_ctor_set(v___x_5959_, 1, v___x_5846_);
v___x_5960_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5961_ = l_Bool_repr___redArg(v_decide_5825_);
v___x_5962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5960_);
lean_ctor_set(v___x_5962_, 1, v___x_5961_);
v___x_5963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
lean_ctor_set_uint8(v___x_5963_, sizeof(void*)*1, v___x_5852_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5959_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set(v___x_5965_, 1, v___x_5855_);
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set(v___x_5966_, 1, v___x_5857_);
v___x_5967_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5846_);
v___x_5970_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5971_ = l_Bool_repr___redArg(v_arith_5826_);
v___x_5972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
v___x_5973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set_uint8(v___x_5973_, sizeof(void*)*1, v___x_5852_);
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5969_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
lean_ctor_set(v___x_5975_, 1, v___x_5855_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set(v___x_5976_, 1, v___x_5857_);
v___x_5977_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5976_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5846_);
v___x_5980_ = l_Bool_repr___redArg(v_autoUnfold_5827_);
v___x_5981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5873_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5982_, 0, v___x_5981_);
lean_ctor_set_uint8(v___x_5982_, sizeof(void*)*1, v___x_5852_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5979_);
lean_ctor_set(v___x_5983_, 1, v___x_5982_);
v___x_5984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set(v___x_5984_, 1, v___x_5855_);
v___x_5985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
lean_ctor_set(v___x_5985_, 1, v___x_5857_);
v___x_5986_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5985_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set(v___x_5988_, 1, v___x_5846_);
v___x_5989_ = l_Bool_repr___redArg(v_dsimp_5828_);
v___x_5990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5970_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
lean_ctor_set_uint8(v___x_5991_, sizeof(void*)*1, v___x_5852_);
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5988_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set(v___x_5993_, 1, v___x_5855_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set(v___x_5994_, 1, v___x_5857_);
v___x_5995_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5994_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set(v___x_5997_, 1, v___x_5846_);
v___x_5998_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5999_ = l_Bool_repr___redArg(v_failIfUnchanged_5829_);
v___x_6000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5998_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v___x_6001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set_uint8(v___x_6001_, sizeof(void*)*1, v___x_5852_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_5997_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v___x_5855_);
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set(v___x_6004_, 1, v___x_5857_);
v___x_6005_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6004_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5846_);
v___x_6008_ = l_Bool_repr___redArg(v_ground_5830_);
v___x_6009_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_5960_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set_uint8(v___x_6010_, sizeof(void*)*1, v___x_5852_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6007_);
lean_ctor_set(v___x_6011_, 1, v___x_6010_);
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6011_);
lean_ctor_set(v___x_6012_, 1, v___x_5855_);
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set(v___x_6013_, 1, v___x_5857_);
v___x_6014_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6013_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5846_);
v___x_6017_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6018_ = l_Bool_repr___redArg(v_unfoldPartialApp_5831_);
v___x_6019_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6017_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set_uint8(v___x_6020_, sizeof(void*)*1, v___x_5852_);
v___x_6021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6016_);
lean_ctor_set(v___x_6021_, 1, v___x_6020_);
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
lean_ctor_set(v___x_6022_, 1, v___x_5855_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_5857_);
v___x_6024_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6023_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_5846_);
v___x_6027_ = l_Bool_repr___redArg(v_zetaDelta_5832_);
v___x_6028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_5932_);
lean_ctor_set(v___x_6028_, 1, v___x_6027_);
v___x_6029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set_uint8(v___x_6029_, sizeof(void*)*1, v___x_5852_);
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6026_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set(v___x_6031_, 1, v___x_5855_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_5857_);
v___x_6033_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6032_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set(v___x_6035_, 1, v___x_5846_);
v___x_6036_ = l_Bool_repr___redArg(v_index_5833_);
v___x_6037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_5970_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set_uint8(v___x_6038_, sizeof(void*)*1, v___x_5852_);
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6035_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set(v___x_6040_, 1, v___x_5855_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_5857_);
v___x_6042_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6041_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_5846_);
v___x_6045_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6046_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5834_);
v___x_6047_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6045_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set_uint8(v___x_6048_, sizeof(void*)*1, v___x_5852_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6044_);
lean_ctor_set(v___x_6049_, 1, v___x_6048_);
v___x_6050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
lean_ctor_set(v___x_6050_, 1, v___x_5855_);
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set(v___x_6051_, 1, v___x_5857_);
v___x_6052_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6051_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5846_);
v___x_6055_ = l_Bool_repr___redArg(v_zetaUnused_5835_);
v___x_6056_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_5873_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set_uint8(v___x_6057_, sizeof(void*)*1, v___x_5852_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6054_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set(v___x_6059_, 1, v___x_5855_);
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
lean_ctor_set(v___x_6060_, 1, v___x_5857_);
v___x_6061_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6060_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5846_);
v___x_6064_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6065_ = l_Bool_repr___redArg(v_catchRuntime_5836_);
v___x_6066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6064_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set_uint8(v___x_6067_, sizeof(void*)*1, v___x_5852_);
v___x_6068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6063_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set(v___x_6069_, 1, v___x_5855_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set(v___x_6070_, 1, v___x_5857_);
v___x_6071_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6070_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_5846_);
v___x_6074_ = l_Bool_repr___redArg(v_zetaHave_5837_);
v___x_6075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_5848_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
v___x_6076_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set_uint8(v___x_6076_, sizeof(void*)*1, v___x_5852_);
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6073_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
lean_ctor_set(v___x_6078_, 1, v___x_5855_);
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set(v___x_6079_, 1, v___x_5857_);
v___x_6080_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6079_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5846_);
v___x_6083_ = l_Bool_repr___redArg(v_letToHave_5838_);
v___x_6084_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_5932_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set_uint8(v___x_6085_, sizeof(void*)*1, v___x_5852_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6082_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
lean_ctor_set(v___x_6087_, 1, v___x_5855_);
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set(v___x_6088_, 1, v___x_5857_);
v___x_6089_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6088_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_5846_);
v___x_6092_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6093_ = l_Bool_repr___redArg(v_congrConsts_5839_);
v___x_6094_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6092_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set_uint8(v___x_6095_, sizeof(void*)*1, v___x_5852_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6091_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6096_);
lean_ctor_set(v___x_6097_, 1, v___x_5855_);
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set(v___x_6098_, 1, v___x_5857_);
v___x_6099_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6098_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5846_);
v___x_6102_ = l_Bool_repr___redArg(v_bitVecOfNat_5840_);
v___x_6103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6092_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set_uint8(v___x_6104_, sizeof(void*)*1, v___x_5852_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6101_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
v___x_6106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set(v___x_6106_, 1, v___x_5855_);
v___x_6107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set(v___x_6107_, 1, v___x_5857_);
v___x_6108_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6107_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_5846_);
v___x_6111_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6112_ = l_Bool_repr___redArg(v_warnExponents_5841_);
v___x_6113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6111_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set_uint8(v___x_6114_, sizeof(void*)*1, v___x_5852_);
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6110_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v___x_5855_);
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_5857_);
v___x_6118_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6117_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_5846_);
v___x_6121_ = l_Bool_repr___redArg(v_suggestions_5842_);
v___x_6122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6092_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set_uint8(v___x_6123_, sizeof(void*)*1, v___x_5852_);
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6120_);
lean_ctor_set(v___x_6124_, 1, v___x_6123_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6124_);
lean_ctor_set(v___x_6125_, 1, v___x_5855_);
v___x_6126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set(v___x_6126_, 1, v___x_5857_);
v___x_6127_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6126_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_5846_);
v___x_6130_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6131_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5843_, v___x_5874_);
v___x_6132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6130_);
lean_ctor_set(v___x_6132_, 1, v___x_6131_);
v___x_6133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set_uint8(v___x_6133_, sizeof(void*)*1, v___x_5852_);
v___x_6134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6129_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set(v___x_6135_, 1, v___x_5855_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set(v___x_6136_, 1, v___x_5857_);
v___x_6137_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6136_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
v___x_6139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set(v___x_6139_, 1, v___x_5846_);
v___x_6140_ = l_Bool_repr___redArg(v_locals_5844_);
v___x_6141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_5960_);
lean_ctor_set(v___x_6141_, 1, v___x_6140_);
v___x_6142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6142_, 0, v___x_6141_);
lean_ctor_set_uint8(v___x_6142_, sizeof(void*)*1, v___x_5852_);
v___x_6143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6139_);
lean_ctor_set(v___x_6143_, 1, v___x_6142_);
v___x_6144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6143_);
lean_ctor_set(v___x_6144_, 1, v___x_5855_);
v___x_6145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set(v___x_6145_, 1, v___x_5857_);
v___x_6146_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6145_);
lean_ctor_set(v___x_6147_, 1, v___x_6146_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_5846_);
v___x_6149_ = l_Bool_repr___redArg(v_instances_5845_);
v___x_6150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_5932_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set_uint8(v___x_6151_, sizeof(void*)*1, v___x_5852_);
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6148_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
v___x_6153_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6154_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set(v___x_6155_, 1, v___x_6152_);
v___x_6156_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6155_);
lean_ctor_set(v___x_6157_, 1, v___x_6156_);
v___x_6158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6153_);
lean_ctor_set(v___x_6158_, 1, v___x_6157_);
v___x_6159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6159_, 0, v___x_6158_);
lean_ctor_set_uint8(v___x_6159_, sizeof(void*)*1, v___x_5852_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6160_, lean_object* v_prec_6161_){
_start:
{
lean_object* v___x_6162_; 
v___x_6162_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6160_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6163_, lean_object* v_prec_6164_){
_start:
{
lean_object* v_res_6165_; 
v_res_6165_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6163_, v_prec_6164_);
lean_dec(v_prec_6164_);
return v_res_6165_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6168_, lean_object* v_x_6169_){
_start:
{
if (lean_obj_tag(v_x_6169_) == 0)
{
uint8_t v___x_6170_; 
v___x_6170_ = 0;
return v___x_6170_;
}
else
{
lean_object* v_head_6171_; lean_object* v_tail_6172_; uint8_t v___x_6173_; 
v_head_6171_ = lean_ctor_get(v_x_6169_, 0);
v_tail_6172_ = lean_ctor_get(v_x_6169_, 1);
v___x_6173_ = lean_nat_dec_eq(v_a_6168_, v_head_6171_);
if (v___x_6173_ == 0)
{
v_x_6169_ = v_tail_6172_;
goto _start;
}
else
{
return v___x_6173_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6175_, lean_object* v_x_6176_){
_start:
{
uint8_t v_res_6177_; lean_object* v_r_6178_; 
v_res_6177_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6175_, v_x_6176_);
lean_dec(v_x_6176_);
lean_dec(v_a_6175_);
v_r_6178_ = lean_box(v_res_6177_);
return v_r_6178_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6179_, lean_object* v_x_6180_){
_start:
{
switch(lean_obj_tag(v_x_6179_))
{
case 0:
{
uint8_t v___x_6181_; 
v___x_6181_ = 1;
return v___x_6181_;
}
case 1:
{
lean_object* v_idxs_6182_; uint8_t v___x_6183_; 
v_idxs_6182_ = lean_ctor_get(v_x_6179_, 0);
v___x_6183_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6180_, v_idxs_6182_);
return v___x_6183_;
}
default: 
{
lean_object* v_idxs_6184_; uint8_t v___x_6185_; 
v_idxs_6184_ = lean_ctor_get(v_x_6179_, 0);
v___x_6185_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6180_, v_idxs_6184_);
if (v___x_6185_ == 0)
{
uint8_t v___x_6186_; 
v___x_6186_ = 1;
return v___x_6186_;
}
else
{
uint8_t v___x_6187_; 
v___x_6187_ = 0;
return v___x_6187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6188_, lean_object* v_x_6189_){
_start:
{
uint8_t v_res_6190_; lean_object* v_r_6191_; 
v_res_6190_ = l_Lean_Meta_Occurrences_contains(v_x_6188_, v_x_6189_);
lean_dec(v_x_6189_);
lean_dec(v_x_6188_);
v_r_6191_ = lean_box(v_res_6190_);
return v_r_6191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6192_){
_start:
{
if (lean_obj_tag(v_x_6192_) == 0)
{
uint8_t v___x_6193_; 
v___x_6193_ = 1;
return v___x_6193_;
}
else
{
uint8_t v___x_6194_; 
v___x_6194_ = 0;
return v___x_6194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6195_){
_start:
{
uint8_t v_res_6196_; lean_object* v_r_6197_; 
v_res_6196_ = l_Lean_Meta_Occurrences_isAll(v_x_6195_);
lean_dec(v_x_6195_);
v_r_6197_ = lean_box(v_res_6196_);
return v_r_6197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6198_){
_start:
{
switch(v_x_6198_)
{
case 0:
{
lean_object* v___x_6199_; 
v___x_6199_ = lean_unsigned_to_nat(0u);
return v___x_6199_;
}
case 1:
{
lean_object* v___x_6200_; 
v___x_6200_ = lean_unsigned_to_nat(1u);
return v___x_6200_;
}
default: 
{
lean_object* v___x_6201_; 
v___x_6201_ = lean_unsigned_to_nat(2u);
return v___x_6201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6202_){
_start:
{
uint8_t v_x_boxed_6203_; lean_object* v_res_6204_; 
v_x_boxed_6203_ = lean_unbox(v_x_6202_);
v_res_6204_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6203_);
return v_res_6204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6205_){
_start:
{
lean_inc(v_k_6205_);
return v_k_6205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6206_);
lean_dec(v_k_6206_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6208_, lean_object* v_ctorIdx_6209_, uint8_t v_t_6210_, lean_object* v_h_6211_, lean_object* v_k_6212_){
_start:
{
lean_inc(v_k_6212_);
return v_k_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6213_, lean_object* v_ctorIdx_6214_, lean_object* v_t_6215_, lean_object* v_h_6216_, lean_object* v_k_6217_){
_start:
{
uint8_t v_t_boxed_6218_; lean_object* v_res_6219_; 
v_t_boxed_6218_ = lean_unbox(v_t_6215_);
v_res_6219_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6213_, v_ctorIdx_6214_, v_t_boxed_6218_, v_h_6216_, v_k_6217_);
lean_dec(v_k_6217_);
lean_dec(v_ctorIdx_6214_);
return v_res_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6220_){
_start:
{
lean_inc(v_nonDependentFirst_6220_);
return v_nonDependentFirst_6220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6221_){
_start:
{
lean_object* v_res_6222_; 
v_res_6222_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6221_);
lean_dec(v_nonDependentFirst_6221_);
return v_res_6222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6223_, uint8_t v_t_6224_, lean_object* v_h_6225_, lean_object* v_nonDependentFirst_6226_){
_start:
{
lean_inc(v_nonDependentFirst_6226_);
return v_nonDependentFirst_6226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6227_, lean_object* v_t_6228_, lean_object* v_h_6229_, lean_object* v_nonDependentFirst_6230_){
_start:
{
uint8_t v_t_boxed_6231_; lean_object* v_res_6232_; 
v_t_boxed_6231_ = lean_unbox(v_t_6228_);
v_res_6232_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6227_, v_t_boxed_6231_, v_h_6229_, v_nonDependentFirst_6230_);
lean_dec(v_nonDependentFirst_6230_);
return v_res_6232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6233_){
_start:
{
lean_inc(v_nonDependentOnly_6233_);
return v_nonDependentOnly_6233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6234_){
_start:
{
lean_object* v_res_6235_; 
v_res_6235_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6234_);
lean_dec(v_nonDependentOnly_6234_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6236_, uint8_t v_t_6237_, lean_object* v_h_6238_, lean_object* v_nonDependentOnly_6239_){
_start:
{
lean_inc(v_nonDependentOnly_6239_);
return v_nonDependentOnly_6239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6240_, lean_object* v_t_6241_, lean_object* v_h_6242_, lean_object* v_nonDependentOnly_6243_){
_start:
{
uint8_t v_t_boxed_6244_; lean_object* v_res_6245_; 
v_t_boxed_6244_ = lean_unbox(v_t_6241_);
v_res_6245_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6240_, v_t_boxed_6244_, v_h_6242_, v_nonDependentOnly_6243_);
lean_dec(v_nonDependentOnly_6243_);
return v_res_6245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6246_){
_start:
{
lean_inc(v_all_6246_);
return v_all_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6247_){
_start:
{
lean_object* v_res_6248_; 
v_res_6248_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6247_);
lean_dec(v_all_6247_);
return v_res_6248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6249_, uint8_t v_t_6250_, lean_object* v_h_6251_, lean_object* v_all_6252_){
_start:
{
lean_inc(v_all_6252_);
return v_all_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6253_, lean_object* v_t_6254_, lean_object* v_h_6255_, lean_object* v_all_6256_){
_start:
{
uint8_t v_t_boxed_6257_; lean_object* v_res_6258_; 
v_t_boxed_6257_ = lean_unbox(v_t_6254_);
v_res_6258_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6253_, v_t_boxed_6257_, v_h_6255_, v_all_6256_);
lean_dec(v_all_6256_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6272_){
_start:
{
lean_object* v___x_6273_; uint8_t v___x_6274_; 
v___x_6273_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6272_);
v___x_6274_ = l_Lean_Syntax_isOfKind(v_c_6272_, v___x_6273_);
if (v___x_6274_ == 0)
{
lean_object* v___x_6275_; uint8_t v___x_6276_; 
v___x_6275_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6272_);
v___x_6276_ = l_Lean_Syntax_isOfKind(v_c_6272_, v___x_6275_);
if (v___x_6276_ == 0)
{
lean_object* v___x_6277_; uint8_t v___x_6278_; 
v___x_6277_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6272_);
v___x_6278_ = l_Lean_Syntax_isOfKind(v_c_6272_, v___x_6277_);
if (v___x_6278_ == 0)
{
lean_object* v___x_6279_; 
lean_dec(v_c_6272_);
v___x_6279_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6279_;
}
else
{
lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; 
v___x_6280_ = lean_unsigned_to_nat(1u);
v___x_6281_ = lean_mk_empty_array_with_capacity(v___x_6280_);
v___x_6282_ = lean_array_push(v___x_6281_, v_c_6272_);
return v___x_6282_;
}
}
else
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6283_ = lean_unsigned_to_nat(0u);
v___x_6284_ = l_Lean_Syntax_getArg(v_c_6272_, v___x_6283_);
lean_dec(v_c_6272_);
v___x_6285_ = l_Lean_Syntax_getArgs(v___x_6284_);
lean_dec(v___x_6284_);
return v___x_6285_;
}
}
else
{
lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; uint8_t v___x_6290_; 
v___x_6286_ = l_Lean_Syntax_getArgs(v_c_6272_);
lean_dec(v_c_6272_);
v___x_6287_ = lean_unsigned_to_nat(0u);
v___x_6288_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6289_ = lean_array_get_size(v___x_6286_);
v___x_6290_ = lean_nat_dec_lt(v___x_6287_, v___x_6289_);
if (v___x_6290_ == 0)
{
lean_dec_ref(v___x_6286_);
return v___x_6288_;
}
else
{
size_t v___x_6291_; size_t v___x_6292_; lean_object* v___x_6293_; 
v___x_6291_ = ((size_t)0ULL);
v___x_6292_ = lean_usize_of_nat(v___x_6289_);
v___x_6293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6286_, v___x_6291_, v___x_6292_, v___x_6288_);
lean_dec_ref(v___x_6286_);
return v___x_6293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6294_, size_t v_i_6295_, size_t v_stop_6296_, lean_object* v_b_6297_){
_start:
{
uint8_t v___x_6298_; 
v___x_6298_ = lean_usize_dec_eq(v_i_6295_, v_stop_6296_);
if (v___x_6298_ == 0)
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; size_t v___x_6302_; size_t v___x_6303_; 
v___x_6299_ = lean_array_uget_borrowed(v_as_6294_, v_i_6295_);
lean_inc(v___x_6299_);
v___x_6300_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6299_);
v___x_6301_ = l_Array_append___redArg(v_b_6297_, v___x_6300_);
lean_dec_ref(v___x_6300_);
v___x_6302_ = ((size_t)1ULL);
v___x_6303_ = lean_usize_add(v_i_6295_, v___x_6302_);
v_i_6295_ = v___x_6303_;
v_b_6297_ = v___x_6301_;
goto _start;
}
else
{
return v_b_6297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6305_, lean_object* v_i_6306_, lean_object* v_stop_6307_, lean_object* v_b_6308_){
_start:
{
size_t v_i_boxed_6309_; size_t v_stop_boxed_6310_; lean_object* v_res_6311_; 
v_i_boxed_6309_ = lean_unbox_usize(v_i_6306_);
lean_dec(v_i_6306_);
v_stop_boxed_6310_ = lean_unbox_usize(v_stop_6307_);
lean_dec(v_stop_6307_);
v_res_6311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6305_, v_i_boxed_6309_, v_stop_boxed_6310_, v_b_6308_);
lean_dec_ref(v_as_6305_);
return v_res_6311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6312_){
_start:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6313_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6314_ = lean_box(2);
v___x_6315_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6316_, 0, v___x_6314_);
lean_ctor_set(v___x_6316_, 1, v___x_6315_);
lean_ctor_set(v___x_6316_, 2, v_items_6312_);
v___x_6317_ = l_Lean_Syntax_node1(v___x_6314_, v___x_6313_, v___x_6316_);
return v___x_6317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6318_, lean_object* v_cfg_x27_6319_){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6320_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6318_);
v___x_6321_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6319_);
v___x_6322_ = l_Array_append___redArg(v___x_6320_, v___x_6321_);
lean_dec_ref(v___x_6321_);
v___x_6323_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6322_);
return v___x_6323_;
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
